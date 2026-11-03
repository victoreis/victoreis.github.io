import Mathlib

/-!
# Spencer's discrepancy theorem: complete upper and lower bounds

Self-contained (relative to Mathlib) combination of the original
`SpencerUpperBound.lean` and `SpencerLowerBound.lean` sources.

Requested toolchain: `leanprover/lean4:v4.36.0-rc2`.
The sources were originally developed against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The final two theorem declarations are:
* `Stoc393.theorem_1_1 : Stoc393.LowerBoundClaim`
* `Stoc393.theorem_1_2 : Stoc393.UpperBoundClaim`

The proofs needed by earlier corollaries are named
`Stoc393.lowerBoundClaim_proof` and `Stoc393.upperBoundClaim_proof`.
-/

/- BEGIN original module: Stoc393.Basic -/
section

/-! Definitions and the nearest-sign rounding argument (Lemma 3.2).
The norm on `Fin d → ℝ` is the maximum absolute coordinate norm.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

def InCube {n : ℕ} (z : Fin n → ℝ) : Prop := ∀ j, |z j| ≤ 1

def IsSigning {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, x j = 1 ∨ x j = -1

def EntryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : Prop :=
  ∀ i j, |A i j| ≤ 1

noncomputable def residual {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  n - ∑ j, z j ^ 2

noncomputable def nearestSign {n : ℕ} (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  if 0 ≤ z j then 1 else -1

theorem nearestSign_isSigning {n : ℕ} (z : Fin n → ℝ) :
    IsSigning (nearestSign z) := by
  intro j
  unfold nearestSign
  split_ifs <;> simp

theorem sq_le_abs_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : t ^ 2 ≤ |t| := by
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
  nlinarith [sq_abs t]

theorem nearestSign_distance {n : ℕ} {z : Fin n → ℝ} (hz : InCube z)
    (j : Fin n) : |nearestSign z j - z j| = 1 - |z j| := by
  have h := abs_le.mp (hz j)
  unfold nearestSign
  split_ifs with hj
  · rw [abs_of_nonneg hj, abs_of_nonneg (by linarith)]
  · have hj' : z j < 0 := lt_of_not_ge hj
    rw [abs_of_neg hj', abs_of_nonpos (by linarith)]
    ring

theorem rounding_distance_le_residual {n : ℕ} {z : Fin n → ℝ} (hz : InCube z) :
    (∑ j, |nearestSign z j - z j|) ≤ residual z := by
  calc
    (∑ j, |nearestSign z j - z j|) = ∑ j, (1 - |z j|) := by
      apply Finset.sum_congr rfl
      intro j _
      exact nearestSign_distance hz j
    _ ≤ ∑ j, (1 - z j ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      linarith [sq_le_abs_of_abs_le_one (hz j)]
    _ = residual z := by simp [residual, Finset.sum_sub_distrib]

theorem residual_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : InCube z) :
    0 ≤ residual z := by
  exact (Finset.sum_nonneg (fun j _ => abs_nonneg _)).trans
    (rounding_distance_le_residual hz)

theorem row_action_le_l1 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (v : Fin n → ℝ) (i : Fin d) :
    |A.mulVec v i| ≤ ∑ j, |v j| := by
  calc
    |A.mulVec v i| = |∑ j, A i j * v j| := rfl
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |v j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg (v j))

theorem matrix_action_le_l1 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (v : Fin n → ℝ) :
    ‖A.mulVec v‖ ≤ ∑ j, |v j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))).mpr
  intro i
  simpa only [Real.norm_eq_abs] using row_action_le_l1 hA v i

/-- Lemma 3.2, with the paper's residual and its specified tie-breaking at zero. -/
theorem lemma_3_2 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) {z : Fin n → ℝ} (hz : InCube z) :
    ‖A.mulVec (nearestSign z)‖ ≤ ‖A.mulVec z‖ + residual z := by
  have hdecomp : A.mulVec (nearestSign z) =
      A.mulVec z + A.mulVec (nearestSign z - z) := by
    rw [Matrix.mulVec_sub]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((matrix_action_le_l1 hA _).trans (rounding_distance_le_residual hz)))

/-- The final rounding implication, with its fractional-point hypotheses explicit. -/
theorem signing_of_fractional_point {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) {z : Fin n → ℝ} (hz : InCube z)
    {D : ℝ} (hrow : ‖A.mulVec z‖ ≤ D) (hres : residual z ≤ 4) :
    ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ D + 4 := by
  exact ⟨nearestSign z, nearestSign_isSigning z,
    (lemma_3_2 hA hz).trans (add_le_add hrow hres)⟩

theorem signing_small_dimension {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (hn : n ≤ 4) {D : ℝ} (hD : 0 ≤ D) :
    ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ D + 4 := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  have h := matrix_action_le_l1 hA (fun _ => 1)
  simp only [abs_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  linarith

end Stoc393

end
/- END original module: Stoc393.Basic -/

/- BEGIN original module: Stoc393.Targets -/
section

/-! Exact main targets. `UpperBound.lean` proves `UpperBoundClaim`;
`LowerBound.lean` proves `LowerBoundClaim`.
The lower-bound probability is represented by exact uniform counting of all
random replacement matrices. The all-signings event is the meaning of
`disc(A) > threshold`, without needing to choose a minimizer.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

noncomputable def upperThreshold (d n : ℕ) : ℝ :=
  Real.sqrt (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ))) + 4

def UpperBoundClaim : Prop :=
  ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℝ), EntryBounded A →
    ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ upperThreshold d n

noncomputable def delta : ℝ := (2 : ℝ) ^ (-(22 : ℤ))

def IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
  ∀ j k, (∑ i, H i j * H i k) = if j = k then (n : ℝ) else 0

abbrev ReplacementBits {n : ℕ} (C : Finset (Fin n)) := Fin n → C → Bool

def bitSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def replaceColumns {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (R : ReplacementBits C) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if hj : j ∈ C then bitSign (R i ⟨j, hj⟩) else H i j

def AllSigningsExceed {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (B : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, IsSigning x → B < ‖A.mulVec x‖

noncomputable def successFraction {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun R : ReplacementBits C =>
    AllSigningsExceed (replaceColumns H C R) ((1 + delta) * Real.sqrt n))).card : ℝ) /
      (Fintype.card (ReplacementBits C) : ℝ)

def LowerBoundClaim : Prop :=
  ∀ (n : ℕ), (∃ r : ℕ, n = 2 ^ r) → 2 ^ 50 ≤ n →
    ∀ (H : Matrix (Fin n) (Fin n) ℝ), IsHadamard H →
      ∀ C : Finset (Fin n), (C.card : ℝ) = delta * n →
        1 - (2 : ℝ) ^ (-(n : ℝ) / 20000) ≤ successFraction H C

def CompleteMainClaims : Prop := UpperBoundClaim ∧ LowerBoundClaim

theorem bitSign_isSign (b : Bool) : bitSign b = 1 ∨ bitSign b = -1 := by
  cases b <;> simp [bitSign]

theorem signings_iff_boolean {n : ℕ} (x : Fin n → ℝ) :
    IsSigning x ↔ ∃ b : Fin n → Bool, x = fun j => bitSign (b j) := by
  classical
  constructor
  · intro hx
    refine ⟨fun j => decide (x j = 1), ?_⟩
    funext j
    rcases hx j with hj | hj <;> simp [hj, bitSign]
  · rintro ⟨b, rfl⟩
    exact fun j => bitSign_isSign (b j)

theorem replaced_entries_are_signs {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsHadamard H) (C : Finset (Fin n)) (R : ReplacementBits C) :
    ∀ i j, replaceColumns H C R i j = 1 ∨ replaceColumns H C R i j = -1 := by
  intro i j
  unfold replaceColumns
  split_ifs
  · exact bitSign_isSign _
  · exact hH.1 i j

theorem replacement_space_card {n : ℕ} (C : Finset (Fin n)) :
    Fintype.card (ReplacementBits C) = 2 ^ (n * C.card) := by
  simp [ReplacementBits, ← pow_mul, Nat.mul_comm]

theorem upper_bound_small_dimension {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) (hn : n ≤ 4) :
    ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ upperThreshold d n := by
  exact signing_small_dimension hA hn (Real.sqrt_nonneg _)

end Stoc393

end
/- END original module: Stoc393.Targets -/

/- BEGIN original module: Stoc393.CappedTrace -/
section

/-! The capped trace argument underlying Lemma 3.4.
The orthonormal-basis construction follows the proof in the PDF, with the
heavy/light decomposition also used in the earlier local Spencer3.lean file.
-/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

/-- Capped trace in a finite-dimensional real inner product space. -/
theorem capped_trace {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (w : ι → ℝ) (K L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : 0 < K) (hL : 0 < L)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K)
    (hq : ∀ v : E, L * ‖v‖ ^ 2 ≤ ∑ i, w i * (inner ℝ (a i) v) ^ 2) :
    (finrank ℝ E : ℝ) ≤ K / L * ∑ i, min (w i) (L / K) := by
  classical
  let c := L / K
  let H : Finset ι := Finset.univ.filter (fun i => c ≤ w i)
  have mem_H (i : ι) : i ∈ H ↔ c ≤ w i := by simp [H]
  have hsplit : (∑ i, min (w i) c) =
      (H.card : ℝ) * c + ∑ i ∈ Hᶜ, w i := by
    calc
      (∑ i, min (w i) c) = (∑ i ∈ H, c) + ∑ i ∈ Hᶜ, w i := by
        rw [← Finset.sum_add_sum_compl H (fun i => min (w i) c)]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          exact min_eq_right ((mem_H i).mp hi)
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' : ¬ c ≤ w i := by simpa only [Finset.mem_compl, mem_H] using hi
          exact min_eq_left (le_of_lt (lt_of_not_ge hi'))
      _ = (H.card : ℝ) * c + ∑ i ∈ Hᶜ, w i := by simp
  let S : Submodule ℝ E := Submodule.span ℝ (↑(H.image a) : Set E)
  let W : Submodule ℝ E := Sᗮ
  have hSdim : finrank ℝ S ≤ H.card :=
    (finrank_span_finset_le_card (R := ℝ) (H.image a)).trans Finset.card_image_le
  have hdim_sum : finrank ℝ S + finrank ℝ W = finrank ℝ E :=
    S.finrank_add_finrank_orthogonal
  have hdim : (finrank ℝ E : ℝ) ≤ H.card + (finrank ℝ W : ℝ) := by
    exact_mod_cast (show finrank ℝ E ≤ H.card + finrank ℝ W by omega)
  let b := stdOrthonormalBasis ℝ W
  let u : Fin (finrank ℝ W) → E := fun j => (b j : E)
  have hu : Orthonormal ℝ u := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hheavy (i : ι) (hi : i ∈ H) (j : Fin (finrank ℝ W)) :
      inner ℝ (a i) (u j) = 0 := by
    apply S.inner_right_of_mem_orthogonal
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact (b j).property
  have hbessel (i : ι) : ∑ j, (inner ℝ (a i) (u j)) ^ 2 ≤ K := by
    have h := hu.sum_inner_products_le (a i) (s := Finset.univ)
    simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm] using h.trans (ha i)
  have hrow (i : ι) : (∑ j, w i * (inner ℝ (a i) (u j)) ^ 2) ≤
      if i ∈ H then 0 else K * w i := by
    by_cases hi : i ∈ H
    · simp [hi, hheavy i hi]
    · rw [ite_eq_right hi, ← Finset.mul_sum]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbessel i) (hw i)
  have htrace : (finrank ℝ W : ℝ) * L ≤ K * ∑ i ∈ Hᶜ, w i := by
    calc
      (finrank ℝ W : ℝ) * L = ∑ j : Fin (finrank ℝ W), L := by simp
      _ ≤ ∑ j, ∑ i, w i * (inner ℝ (a i) (u j)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [hu.norm_eq_one j, one_pow, mul_one] using hq (u j)
      _ = ∑ i, ∑ j, w i * (inner ℝ (a i) (u j)) ^ 2 := Finset.sum_comm
      _ ≤ ∑ i, if i ∈ H then 0 else K * w i := Finset.sum_le_sum (fun i _ => hrow i)
      _ = K * ∑ i ∈ Hᶜ, w i := by
        calc
          (∑ i, if i ∈ H then 0 else K * w i) =
              ∑ i, if i ∈ Hᶜ then K * w i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ H <;> simp [hi]
          _ = ∑ i ∈ Hᶜ, K * w i := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr (by ext i; simp)
            intro i _
            rfl
          _ = K * ∑ i ∈ Hᶜ, w i := (Finset.mul_sum _ _ _).symm
  have hcK : K * c = L := by dsimp [c]; field_simp
  have htotal : (finrank ℝ E : ℝ) * L ≤ K * ∑ i, min (w i) c := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right hdim hL.le]
  simpa only [div_mul_eq_mul_div] using (le_div_iff₀ hL).mpr htotal

/-- The same estimate for a subspace, using orthogonal projections of the rows. -/
theorem capped_trace_subspace {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (a : ι → E) (w : ι → ℝ) (K L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : 0 < K) (hL : 0 < L)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K)
    (hq : ∀ v : V, L * ‖v‖ ^ 2 ≤ ∑ i, w i * (inner ℝ (a i) (v : E)) ^ 2) :
    (finrank ℝ V : ℝ) ≤ K / L * ∑ i, min (w i) (L / K) := by
  apply capped_trace (fun i => V.orthogonalProjectionOnto (a i)) w K L hw hK hL
  · intro i
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (V.norm_orthogonalProjectionOnto_apply_le (a i)) |>.trans (ha i)
  · intro v
    simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hq v

/-- Lemma 3.4 in the paper's supported-subspace formulation, for nonempty J. -/
theorem lemma_3_4_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hsupport : ∀ v : V, ∀ j ∉ J, (v : EuclideanSpace ℝ (Fin n)) j = 0)
    (w : Fin m → ℝ) (L : ℝ) (hw : ∀ i, 0 ≤ w i) (hL : 0 < L)
    (hq : ∀ v : V, L * ‖v‖ ^ 2 ≤
      ∑ i, w i * (∑ j, A i j * (v : EuclideanSpace ℝ (Fin n)) j) ^ 2) :
    (finrank ℝ V : ℝ) ≤ J.card / L * ∑ i, min (w i) (L / J.card) := by
  classical
  let a : Fin m → EuclideanSpace ℝ (Fin n) :=
    fun i => WithLp.toLp 2 (fun j => if j ∈ J then A i j else 0)
  have ha : ∀ i, ‖a i‖ ^ 2 ≤ (J.card : ℝ) := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j, (a i j) ^ 2) = ∑ j ∈ J, (A i j) ^ 2 := by
        simp [a]
      _ ≤ ∑ _j ∈ J, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_abs_of_abs_le_one (hA i j)).trans (hA i j)
      _ = (J.card : ℝ) := by simp
  have hip (i : Fin m) (v : V) :
      inner ℝ (a i) (v : EuclideanSpace ℝ (Fin n)) =
      ∑ j, A i j * (v : EuclideanSpace ℝ (Fin n)) j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simp [a, hj, mul_comm]
    · simp [a, hj, hsupport v j hj]
  apply capped_trace_subspace V a w J.card L hw (by exact_mod_cast hJ.card_pos) hL ha
  intro v
  simpa only [hip] using hq v

/-- The full capped trace statement, also covering the empty supported subspace. -/
theorem lemma_3_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (J : Finset (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hsupport : ∀ v : V, ∀ j ∉ J, (v : EuclideanSpace ℝ (Fin n)) j = 0)
    (w : Fin m → ℝ) (L : ℝ) (hw : ∀ i, 0 ≤ w i) (hL : 0 < L)
    (hq : ∀ v : V, L * ‖v‖ ^ 2 ≤
      ∑ i, w i * (∑ j, A i j * (v : EuclideanSpace ℝ (Fin n)) j) ^ 2) :
    (finrank ℝ V : ℝ) ≤ J.card / L * ∑ i, min (w i) (L / J.card) := by
  classical
  by_cases hJ : J.Nonempty
  · exact lemma_3_4_nonempty A hA J hJ V hsupport w L hw hL hq
  · have hJ0 : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    have hV : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro v hv
      have hv0 : v = 0 := by
        ext j
        exact hsupport ⟨v, hv⟩ j (by simp [hJ0])
      simpa only [Submodule.mem_bot] using hv0
    simp [hJ0, hV]

end Stoc393

end
/- END original module: Stoc393.CappedTrace -/

/- BEGIN original module: Stoc393.ScalarReduction -/
section

/-! Algebraic implications surrounding the scalar inequality.
The comparison is an explicit hypothesis in this abstract reduction.
`ScalarBarrier.lean` proves it for the paper's concrete function.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

/-- Positive-input formula only. Its value at zero is NOT the paper's infinity. -/
noncomputable def phi (t : ℝ) : ℝ := 5 / Real.sinh (t ^ 2 / 3)

noncomputable def psi (t : ℝ) : ℝ := -t * deriv phi t - 2 * phi t

/-- The scalar comparison, equation (27), proved in `ScalarBarrier.lean`. -/
def ScalarComparisonClaim : Prop :=
  ∀ t : ℝ, 0 < t → (1 - phi t / 4) * deriv (deriv phi) t ≤ 3 / 4 * psi t

theorem phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t := by
  exact div_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))

/-- The two-case reduction in Appendix C, with comparison as an explicit input. -/
theorem cap_of_scalar_comparison {p q r θ : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hc : (1 - p / 4) * r ≤ 3 / 4 * q) :
    min r θ ≤ 3 / 4 * q + θ * p / 4 := by
  by_cases hp4 : 4 ≤ p
  · have hmul := mul_le_mul_of_nonneg_left hp4 hθ
    have hm := min_le_right r θ
    nlinarith
  · have hp4' : p < 4 := lt_of_not_ge hp4
    have hleft := mul_le_mul_of_nonneg_left (min_le_left r θ)
      (show 0 ≤ 1 - p / 4 by linarith)
    have hright := mul_le_mul_of_nonneg_left (min_le_right r θ)
      (show 0 ≤ p / 4 by positivity)
    nlinarith

/-- The last dimension-count contradiction on page 9, with every bound explicit. -/
theorem dimension_contradiction {ι : Type*} [Fintype ι]
    (w p q : ι → ℝ) (J L D : ℝ)
    (hJ : 0 < J) (hL : 0 < L) (hq : ∑ i, q i = L)
    (hdim : J - 1 ≤ D)
    (htrace : D ≤ J / L * ∑ i, min (w i) (L / J))
    (hcap : ∀ i, min (w i) (L / J) ≤ 3 / 4 * q i + (L / J) * p i / 4)
    (hpotential : (∑ i, p i) < J - 4) : False := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcap i)
  have hsum' : (∑ i, min (w i) (L / J)) ≤
      3 / 4 * L + (L / J) * (∑ i, p i) / 4 := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hq] using hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum' (div_pos hJ hL).le
  have heq : J / L * (3 / 4 * L + (L / J) * (∑ i, p i) / 4) =
      3 * J / 4 + (∑ i, p i) / 4 := by
    field_simp
  rw [heq] at hscaled
  linarith

end Stoc393

end
/- END original module: Stoc393.ScalarReduction -/

/- BEGIN original module: Stoc393.ScalarCalculus -/
section

/-! Elementary scalar calculus from Appendix C.
No assertion of the unproved equation (27) is made in this module.
-/

set_option autoImplicit false

namespace Stoc393

open scoped Topology

noncomputable def phiD (t : ℝ) : ℝ :=
  -10 * t * Real.cosh (t ^ 2 / 3) / (3 * Real.sinh (t ^ 2 / 3) ^ 2)

theorem hasDerivAt_phi {t : ℝ} (ht : 0 < t) : HasDerivAt phi (phiD t) t := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hu := ((hasDerivAt_id t).pow 2).div_const 3
  convert (hasDerivAt_const t (5 : ℝ)).div hu.sinh hs using 1
  · rfl
  · dsimp [phiD]
    ring

theorem deriv_phi {t : ℝ} (ht : 0 < t) : deriv phi t = phiD t :=
  (hasDerivAt_phi ht).deriv

theorem deriv_phi_neg {t : ℝ} (ht : 0 < t) : deriv phi t < 0 := by
  rw [deriv_phi ht, phiD]
  apply div_neg_of_neg_of_pos
  · have hc := Real.cosh_pos (t ^ 2 / 3)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) ht) hc
  · have hs := Real.sinh_pos_iff.mpr (show 0 < t ^ 2 / 3 by positivity)
    positivity

theorem mul_cosh_sub_sinh_pos {u : ℝ} (hu : 0 < u) :
    0 < u * Real.cosh u - Real.sinh u := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    · rfl
    · dsimp
      ring
  have hm : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    exact mul_pos hx (Real.sinh_pos_iff.mpr hx)
  simpa using hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) (show u ∈ Set.Ici (0 : ℝ) from hu.le) hu

theorem psi_formula {t : ℝ} (ht : 0 < t) :
    psi t = 10 / Real.sinh (t ^ 2 / 3) ^ 2 *
      ((t ^ 2 / 3) * Real.cosh (t ^ 2 / 3) - Real.sinh (t ^ 2 / 3)) := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  rw [psi, deriv_phi ht, phiD, phi]
  field_simp
  ring

theorem psi_pos {t : ℝ} (ht : 0 < t) : 0 < psi t := by
  rw [psi_formula ht]
  have hu : 0 < t ^ 2 / 3 := by positivity
  have hs := Real.sinh_pos_iff.mpr hu
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos hs)) (mul_cosh_sub_sinh_pos hu)

noncomputable def phiDD (t : ℝ) : ℝ :=
  10 / (3 * Real.sinh (t ^ 2 / 3)) *
    (-Real.cosh (t ^ 2 / 3) / Real.sinh (t ^ 2 / 3) +
      2 * (t ^ 2 / 3) * (1 + 2 / Real.sinh (t ^ 2 / 3) ^ 2))

theorem hasDerivAt_phiD {t : ℝ} (ht : 0 < t) : HasDerivAt phiD (phiDD t) t := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hu := ((hasDerivAt_id t).pow 2).div_const 3
  have hnum := ((hasDerivAt_id t).const_mul (-10)).mul hu.cosh
  have hden := (hu.sinh.pow 2).const_mul 3
  convert hnum.div hden (by exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)) using 1
  · rfl
  · dsimp [phiDD]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (t ^ 2 / 3)]

theorem second_deriv_phi {t : ℝ} (ht : 0 < t) : deriv (deriv phi) t = phiDD t := by
  have heq : deriv phi =ᶠ[𝓝 t] phiD := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact deriv_phi hx
  rw [heq.deriv_eq]
  exact (hasDerivAt_phiD ht).deriv

theorem curvature_numerator_pos {u : ℝ} (hu : 0 < u) :
    0 < 2 * u * (Real.sinh u ^ 2 + 2) - Real.sinh u * Real.cosh u := by
  let f : ℝ → ℝ := fun x =>
    2 * x * (Real.sinh x ^ 2 + 2) - Real.sinh x * Real.cosh x
  have hd (x : ℝ) : HasDerivAt f (3 + 4 * x * Real.sinh x * Real.cosh x) x := by
    convert (((hasDerivAt_id x).const_mul 2).mul
      (((Real.hasDerivAt_sinh x).pow 2).add_const 2)).sub
      ((Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_cosh x)) using 1
    · rfl
    · dsimp
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hm : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by dsimp [f]; fun_prop)
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    have hs := Real.sinh_pos_iff.mpr hx
    have hc := Real.cosh_pos x
    positivity
  have h := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hu.le hu
  simpa [f] using h

theorem second_deriv_phi_pos {t : ℝ} (ht : 0 < t) : 0 < deriv (deriv phi) t := by
  rw [second_deriv_phi ht, phiDD]
  have hu : 0 < t ^ 2 / 3 := by positivity
  have hs := Real.sinh_pos_iff.mpr hu
  apply mul_pos (div_pos (by norm_num) (mul_pos (by norm_num) hs))
  have h := curvature_numerator_pos hu
  have hid : -Real.cosh (t ^ 2 / 3) / Real.sinh (t ^ 2 / 3) +
      2 * (t ^ 2 / 3) * (1 + 2 / Real.sinh (t ^ 2 / 3) ^ 2) =
      (2 * (t ^ 2 / 3) * (Real.sinh (t ^ 2 / 3) ^ 2 + 2) -
        Real.sinh (t ^ 2 / 3) * Real.cosh (t ^ 2 / 3)) /
        Real.sinh (t ^ 2 / 3) ^ 2 := by
    field_simp
    ring
  rw [hid]
  exact div_pos h (sq_pos_of_pos hs)

/-- Equation (28), the scale derivative. -/
theorem hasDerivAt_scaled_phi {D s : ℝ} (hD : 0 < D) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => (1 / s) * phi (D / Real.sqrt s))
      (psi (D / Real.sqrt s) / (2 * s ^ 2)) s := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have ht : 0 < D / Real.sqrt s := div_pos hD hsqrt
  have hT := (hasDerivAt_const s D).div (Real.hasDerivAt_sqrt hs.ne') hsqrt.ne'
  convert ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs.ne').mul
    ((hasDerivAt_phi ht).comp s hT) using 1
  · rfl
  · dsimp
    rw [psi, deriv_phi ht]
    field_simp
    rw [pow_succ (Real.sqrt s) 2, Real.sq_sqrt hs.le]
    ring

/-- Lemma 3.3(d), including strictness on the full positive half-line. -/
theorem scaled_phi_strictMonoOn {D : ℝ} (hD : 0 < D) :
    StrictMonoOn (fun s : ℝ => (1 / s) * phi (D / Real.sqrt s)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs
    exact (hasDerivAt_scaled_phi hD hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi, Set.mem_Ioi] at hs
    rw [(hasDerivAt_scaled_phi hD hs).deriv]
    exact div_pos (psi_pos (div_pos hD (Real.sqrt_pos.mpr hs))) (by positivity)

theorem phi_at_c : phi (Real.sqrt (3 * Real.arsinh 10)) = 1 / 2 := by
  have ha : 0 < Real.arsinh 10 := Real.arsinh_pos_iff.mpr (by norm_num)
  unfold phi
  rw [Real.sq_sqrt (by positivity)]
  have heq : (3 * Real.arsinh 10) / 3 = Real.arsinh 10 := by ring
  rw [heq, Real.sinh_arsinh]
  norm_num

theorem phi_tendsto_atTop_zero : Filter.Tendsto phi (𝓝[>] (0 : ℝ)) Filter.atTop := by
  have h0 : Filter.Tendsto (fun t : ℝ => Real.sinh (t^2/3))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Continuous (fun t : ℝ => Real.sinh (t^2/3)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.sinh (t^2/3) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply Real.sinh_pos_iff.mpr
    have ht' : 0 < t := ht
    positivity
  have hgt : Filter.Tendsto (fun t : ℝ => Real.sinh (t^2/3))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩
  change Filter.Tendsto (fun t : ℝ => 5 / Real.sinh (t^2/3)) _ _
  simpa only [Function.comp_def, div_eq_mul_inv] using
    (tendsto_inv_nhdsGT_zero.comp hgt).const_mul_atTop (show (0 : ℝ) < 5 by norm_num)

end Stoc393

end
/- END original module: Stoc393.ScalarCalculus -/

/- BEGIN original module: Stoc393.ScalarPQ -/
section

/-! Analytic proof supplied by the user on 2026-10-30: the P + Q estimates. -/

open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def scalarP (u : ℝ) : ℝ := (u-5)*Real.exp u + 20*u-10
noncomputable def scalarQ (u : ℝ) : ℝ :=
  -(49*u-23)*Real.exp (-u) + 120*u*Real.exp (-2*u)
noncomputable def scalarW (u : ℝ) : ℝ :=
  (u-5)*Real.exp u + 76/5*u-10 + (23-u)*(3-u)*Real.exp (-2)
noncomputable def scalarWD (u : ℝ) : ℝ :=
  (u-4)*Real.exp u + 76/5 + (2*u-26)*Real.exp (-2)

theorem exp_one_bounds : 8/3 < Real.exp 1 ∧ Real.exp 1 < 68/25 := by
  have hl := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
  have hr := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl hr
  constructor <;> linarith

theorem exp_two_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_neg_two_lower : (625 : ℝ)/4624 ≤ Real.exp (-2) := by
  have hp : Real.exp 1 ^ 2 * Real.exp (-2) = 1 := by
    rw [← exp_two_eq, ← Real.exp_add]
    norm_num
  have he := exp_one_bounds.2
  have he0 := Real.exp_pos (1 : ℝ)
  have he2 : Real.exp 1 ^ 2 ≤ (68/25 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg (-2))
  nlinarith

theorem hasDerivAt_scalarP (u : ℝ) :
    HasDerivAt scalarP (20+(u-4)*Real.exp u) u := by
  convert (((hasDerivAt_id u).sub_const 5).mul (Real.hasDerivAt_exp u)).add
    ((hasDerivAt_id u).const_mul 20) |>.sub_const 10 using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_scalarW (u : ℝ) : HasDerivAt scalarW (scalarWD u) u := by
  convert ((((hasDerivAt_id u).sub_const 5).mul (Real.hasDerivAt_exp u)).add
    ((hasDerivAt_id u).const_mul (76/5)) |>.sub_const 10).add
    ((((hasDerivAt_id u).const_sub 23).mul
      ((hasDerivAt_id u).const_sub 3)).mul_const (Real.exp (-2))) using 1
  · rfl
  · dsimp [scalarWD]
    ring

theorem hasDerivAt_scalarWD (u : ℝ) :
    HasDerivAt scalarWD ((u-3)*Real.exp u + 2*Real.exp (-2)) u := by
  convert ((((hasDerivAt_id u).sub_const 4).mul (Real.hasDerivAt_exp u)).add_const
    (76/5)).add ((((hasDerivAt_id u).const_mul 2).sub_const 26).mul_const
      (Real.exp (-2))) using 1
  · rfl
  · dsimp
    ring

theorem scalarW_concave : ConcaveOn ℝ (Set.Icc 1 2) scalarW := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 1 2)
    (by unfold scalarW; fun_prop)
    (fun x _ => (hasDerivAt_scalarW x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_scalarWD x).hasDerivWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  have he : 8/3 < Real.exp x :=
    exp_one_bounds.1.trans_le (Real.exp_le_exp.mpr hx.1.le)
  have hn : Real.exp (-2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hp := mul_le_mul_of_nonneg_right (show x-3 ≤ -1 by linarith [hx.2])
    (Real.exp_nonneg x)
  nlinarith

theorem scalarW_endpoints : 1/4 < scalarW 1 ∧ 1 < scalarW 2 := by
  have he := exp_one_bounds.2
  have he0 := Real.exp_pos (1 : ℝ)
  have he2 : Real.exp 1 ^ 2 ≤ (68/25 : ℝ)^2 := by nlinarith
  have hn := exp_neg_two_lower
  unfold scalarW
  rw [exp_two_eq]
  constructor <;> nlinarith

theorem scalarW_pos {u : ℝ} (hu : u ∈ Set.Icc 1 2) : 0 < scalarW u := by
  have h := scalarW_concave.min_le_of_mem_Icc
    (show (1 : ℝ) ∈ Set.Icc 1 2 by norm_num)
    (show (2 : ℝ) ∈ Set.Icc 1 2 by norm_num) hu
  have hl : 0 < min (scalarW 1) (scalarW 2) :=
    lt_min (by linarith [scalarW_endpoints.1]) (by linarith [scalarW_endpoints.2])
  exact hl.trans_le h

theorem scalarPQ_ge_W {u : ℝ} (hu : u ∈ Set.Icc 1 2) :
    scalarW u ≤ scalarP u + scalarQ u := by
  have hs : Real.exp (-2*u) = Real.exp (-u)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq := mul_nonneg (show 0 ≤ 120*u by linarith [hu.1])
    (sq_nonneg (Real.exp (-u) - 1/5))
  have ht := Real.add_one_le_exp (2-u)
  have hmul := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg (-2))
  have hexp : Real.exp (2-u) * Real.exp (-2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hmul
  have hmul' := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 23-u by linarith [hu.2])
  unfold scalarW scalarP scalarQ
  rw [hs]
  nlinarith

theorem scalarPQ_pos_small {u : ℝ} (hu : u ∈ Set.Icc 1 2) :
    0 < scalarP u + scalarQ u :=
  (scalarW_pos hu).trans_le (scalarPQ_ge_W hu)

theorem scalarP_derivative_lower (u : ℝ) : -1/8 < 20+(u-4)*Real.exp u := by
  have ht := Real.add_one_le_exp (3-u)
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg u)
  have heq : Real.exp (3-u) * Real.exp u = Real.exp 1 ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hm
  have he0 := Real.exp_pos (1 : ℝ)
  have he := exp_one_bounds.2.le
  have he3 := pow_le_pow_left₀ he0.le he 3
  nlinarith

theorem scalarP_lower_two_four {u : ℝ} (hu : u ∈ Set.Icc 2 4) :
    15/2 < scalarP u := by
  have hm : Monotone (fun x : ℝ => scalarP x + x/8) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hasDerivAt_scalarP x).add ((hasDerivAt_id x).div_const 8))
    intro x
    dsimp
    linarith [scalarP_derivative_lower x]
  have h := hm hu.1
  have he := exp_one_bounds.2.le
  have he2 := pow_le_pow_left₀ (Real.exp_nonneg 1) he 2
  unfold scalarP at h ⊢
  dsimp at h
  rw [exp_two_eq] at h
  nlinarith [hu.2]

theorem scalarP_lower {u : ℝ} (hu : 2 ≤ u) : 15/2 < scalarP u := by
  by_cases h4 : u ≤ 4
  · exact scalarP_lower_two_four ⟨hu, h4⟩
  · have hm : MonotoneOn scalarP (Set.Ici 4) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 4)
        (by unfold scalarP; fun_prop)
        (fun x _ => (hasDerivAt_scalarP x).hasDerivWithinAt)
      intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hp : 0 ≤ (x-4)*Real.exp x :=
        mul_nonneg (by linarith [hx]) (Real.exp_nonneg x)
      linarith
    exact (scalarP_lower_two_four (show (4 : ℝ) ∈ Set.Icc 2 4 by norm_num)).trans_le
      (hm (by simp) (le_of_not_ge h4) (le_of_not_ge h4))

theorem scalarQ_algebra {u r : ℝ} (hr : 0 ≤ r) (hur : u*r ≤ 3/4)
    (hc : 0 ≤ 49-120*r^2) :
    -7 < -(49*u-23)*r^2 + 120*u*r^4 := by
  have hm := mul_le_mul_of_nonneg_right hur (mul_nonneg hc hr)
  have hsq := mul_nonneg (sq_nonneg (r-3/10)) (show 0 ≤ 90*r+77 by linarith)
  nlinarith

theorem scalarQ_lower {u : ℝ} (hu : 2 ≤ u) : -7 < scalarQ u := by
  let r := Real.exp (-u/2)
  have hr : 0 < r := Real.exp_pos _
  have he := exp_one_bounds.1
  have hp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hn0 := Real.exp_pos (-1)
  have hn : Real.exp (-1) < 3/8 := by nlinarith
  have hrle : r ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have ht := Real.add_one_le_exp (u/2-1)
  have hm := mul_le_mul_of_nonneg_right ht hr.le
  have heq : Real.exp (u/2-1)*r = Real.exp (-1) := by
    dsimp [r]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hur : u*r ≤ 3/4 := by nlinarith
  have hc : 0 ≤ 49-120*r^2 := by nlinarith
  have h := scalarQ_algebra hr.le hur hc
  have h2 : Real.exp (-u) = r^2 := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-2*u) = r^4 := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [scalarQ, h2, h4] using h

theorem scalarPQ_pos {u : ℝ} (hu : 1 ≤ u) : 0 < scalarP u + scalarQ u := by
  by_cases h2 : u ≤ 2
  · exact scalarPQ_pos_small ⟨hu, h2⟩
  · have hp := scalarP_lower (le_of_not_ge h2)
    have hq := scalarQ_lower (le_of_not_ge h2)
    linarith

end Stoc393

end
/- END original module: Stoc393.ScalarPQ -/

/- BEGIN original module: Stoc393.ScalarBarrier -/
section

/-! Equation (27), completing the analytic argument supplied by the user.
The proof uses exact real inequalities and algebra, not sampled values.
-/

set_option autoImplicit false
namespace Stoc393

theorem sinh_one_bound : Real.sinh 1 ≤ 5/4 := by
  have he := exp_one_bounds.2
  have hp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hz := Real.exp_pos (-1)
  have hneg : 1/4 ≤ Real.exp (-1) := by nlinarith
  rw [Real.sinh_eq]
  linarith

theorem scalar_gap_identity {t : ℝ} (ht : 0 < t) :
    (48 * Real.exp (-2*(t^2/3)) * Real.sinh (t^2/3)^4 / 5) *
      (3/4*psi t - (1-phi t/4)*deriv (deriv phi) t) =
    scalarP (t^2/3) + scalarQ (t^2/3) +
      31*(t^2/3-1)*Real.exp (-3*(t^2/3)) +
      (20*(t^2/3)+10)*Real.exp (-4*(t^2/3)) +
      (17*(t^2/3)+13)*Real.exp (-5*(t^2/3)) := by
  let u := t^2/3
  have hs : Real.sinh u ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by dsimp [u]; positivity))
  have he : Real.exp (-u) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hscale (k : ℕ) : Real.exp (-(k : ℝ)*u) = Real.exp (-u)^k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hinv : Real.exp u = (Real.exp (-u))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [psi_formula ht, second_deriv_phi ht]
  unfold scalarP scalarQ phi phiDD
  change (48 * Real.exp (-2*u) * Real.sinh u^4 / 5) *
      (3/4*(10/Real.sinh u^2*(u*Real.cosh u-Real.sinh u)) -
       (1-(5/Real.sinh u)/4) *
         (10/(3*Real.sinh u)*(-Real.cosh u/Real.sinh u+2*u*(1+2/Real.sinh u^2)))) =
    (u-5)*Real.exp u+20*u-10 +
    (-(49*u-23)*Real.exp (-u)+120*u*Real.exp (-2*u)) +
    31*(u-1)*Real.exp (-3*u)+(20*u+10)*Real.exp (-4*u)+(17*u+13)*Real.exp (-5*u)
  have h2 := hscale 2
  have h3 := hscale 3
  have h4 := hscale 4
  have h5 := hscale 5
  norm_num only [Nat.cast_ofNat] at h2 h3 h4 h5
  rw [h2, h3, h4, h5]
  field_simp
  rw [Real.sinh_eq, Real.cosh_eq, hinv]
  field_simp
  ring

/-- The scalar-barrier inequality, equation (27), with no added hypotheses. -/
theorem scalar_barrier_inequality {t : ℝ} (ht : 0 < t) :
    (1-phi t/4)*deriv (deriv phi) t ≤ 3/4*psi t := by
  by_cases hp : 4 ≤ phi t
  · have hl : (1-phi t/4)*deriv (deriv phi) t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (second_deriv_phi_pos ht).le
    exact hl.trans (mul_nonneg (by norm_num) (psi_pos ht).le)
  · have hu : 1 < t^2/3 := by
      by_contra hu
      have hs : Real.sinh (t^2/3) ≤ 5/4 :=
        (Real.sinh_le_sinh.mpr (le_of_not_gt hu)).trans sinh_one_bound
      have hs0 : 0 < Real.sinh (t^2/3) := Real.sinh_pos_iff.mpr (by positivity)
      have hp' : 4 ≤ phi t := by
        unfold phi
        apply (le_div_iff₀ hs0).mpr
        linarith
      exact hp hp'
    have hPQ := scalarPQ_pos hu.le
    have h1 : 0 ≤ 31*(t^2/3-1)*Real.exp (-3*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have h2 : 0 ≤ (20*(t^2/3)+10)*Real.exp (-4*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have h3 : 0 ≤ (17*(t^2/3)+13)*Real.exp (-5*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have hid := scalar_gap_identity ht
    have hscale : 0 < 48*Real.exp (-2*(t^2/3))*Real.sinh (t^2/3)^4/5 := by
      have hs : 0 < Real.sinh (t^2/3) := Real.sinh_pos_iff.mpr (by positivity)
      positivity
    have hgap : 0 < 3/4*psi t-(1-phi t/4)*deriv (deriv phi) t := by
      apply (mul_pos_iff_of_pos_left hscale).mp
      rw [hid]
      linarith
    linarith

theorem scalarComparison_proved : ScalarComparisonClaim :=
  fun _ ht => scalar_barrier_inequality ht

/-- Lemma 3.3(c), now with the scalar comparison discharged. -/
theorem lemma_3_3_c {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    min (deriv (deriv phi) t) θ ≤ 3/4*psi t + θ*phi t/4 :=
  cap_of_scalar_comparison (phi_pos ht).le (psi_pos ht).le hθ.le
    (scalar_barrier_inequality ht)

end Stoc393

end
/- END original module: Stoc393.ScalarBarrier -/

/- BEGIN original module: Stoc393.SecondVariation -/
section

/-! The second variation of the reciprocal-sinh potential, Lemma 3.5.
The abstract curve rule adapts the checked local Spencer3.lean construction.
-/

open scoped Topology BigOperators
open Filter
set_option autoImplicit false

namespace Stoc393

theorem contDiffAt_phi {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 2 phi t := by
  unfold phi
  apply ContDiffAt.div (by fun_prop) (by fun_prop)
  exact ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))

theorem second_comp_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {p pd : ℝ → E} {v a : E}
    (hF : ContDiffAt ℝ 2 F (p 0)) (hp : HasDerivAt p v 0)
    (hevent : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt p (pd t) t)
    (hpd0 : pd 0 = v) (hpd : HasDerivAt pd a 0) :
    HasDerivAt (deriv (fun t => F (p t)))
      ((fderiv ℝ (fderiv ℝ F) (p 0) v) v + fderiv ℝ F (p 0) a) 0 := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ F) (p 0) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have houter := hf2.hasFDerivAt.comp_hasDerivAt 0 hp
  have hd := houter.clm_apply hpd
  have hlocal : deriv (fun t => F (p t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ F (p t) (pd t)) := by
    have hsmooth := hp.continuousAt.tendsto.eventually (hF.eventually (by norm_num))
    filter_upwards [hsmooth, hevent] with t ht hpt
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hpt).deriv
  simpa only [hpd0, Function.comp_apply] using hd.congr_of_eventuallyEq hlocal

theorem quadratic_scale_second {F : ℝ × ℝ → ℝ} {s a b w : ℝ}
    (hF : ContDiffAt ℝ 2 F (s, a)) :
    HasDerivAt (deriv (fun t : ℝ => F (s-b*t^2, a+t*w)))
      (deriv (deriv (fun t : ℝ => F (s, a+t*w))) 0 -
        2*b*deriv (fun r : ℝ => F (r,a)) s) 0 := by
  let p : ℝ → ℝ × ℝ := fun t => (s-b*t^2,a+t*w)
  let pd : ℝ → ℝ × ℝ := fun t => (-2*b*t,w)
  have hp (t : ℝ) : HasDerivAt p (pd t) t := by
    apply HasDerivAt.prodMk
    · convert (((hasDerivAt_id t).pow 2).const_mul b).const_sub s using 1
      all_goals dsimp [pd, id]
      all_goals ring
    · simpa using ((hasDerivAt_id t).mul_const w).const_add a
  have hpd : HasDerivAt pd (-2*b,0) 0 := by
    simpa [pd] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (-2*b)).prodMk (hasDerivAt_const 0 w)
  have hp0 : p 0 = (s,a) := by simp [p]
  have hpd0 : pd 0 = (0,w) := by simp [pd]
  have hpath := second_comp_curve (hp0.symm ▸ hF) (hpd0 ▸ hp 0)
    (Eventually.of_forall hp) hpd0 hpd
  have hq (t : ℝ) : HasDerivAt (fun t : ℝ => (s,a+t*w)) (0,w) t :=
    (hasDerivAt_const t s).prodMk (by simpa using ((hasDerivAt_id t).mul_const w).const_add a)
  have hfixed := second_comp_curve (by simpa using hF) (hq 0)
    (Eventually.of_forall hq) rfl (hasDerivAt_const (0 : ℝ) ((0 : ℝ),w))
  have hfixed' : deriv (deriv (fun t : ℝ => F (s,a+t*w))) 0 =
      (fderiv ℝ (fderiv ℝ F) (s,a) (0,w)) (0,w) := by
    simpa using hfixed.deriv
  have hpartial : deriv (fun r : ℝ => F (r,a)) s = fderiv ℝ F (s,a) (1,0) :=
    ((hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s a))).deriv
  have hacc : ((-2*b : ℝ),(0 : ℝ)) = (-2*b) • ((1 : ℝ),(0 : ℝ)) := by simp
  have hcoef : (fderiv ℝ (fderiv ℝ F) (s,a) (0,w)) (0,w) +
      fderiv ℝ F (s,a) (-2*b,0) =
      deriv (deriv (fun t : ℝ => F (s,a+t*w))) 0 -
        2*b*deriv (fun r : ℝ => F (r,a)) s := by
    rw [hfixed', hpartial, hacc, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [← hcoef]
  simpa [p, pd] using hpath

noncomputable def rowPotential (q : ℝ × ℝ) : ℝ := (1/q.1)*phi (q.2/Real.sqrt q.1)

theorem rowPotential_contDiffAt {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ContDiffAt ℝ 2 rowPotential (s,a) := by
  have hsqrt : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hgap : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / Real.sqrt q.1) (s,a) :=
    ContDiffAt.div (by fun_prop) ((by fun_prop : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1) (s,a)).sqrt hs.ne') hsqrt
  have hcomp := (contDiffAt_phi (div_pos ha (Real.sqrt_pos.mpr hs))).comp (s,a) hgap
  exact (ContDiffAt.div (by fun_prop) (by fun_prop) hs.ne').mul hcomp

theorem fixed_scale_second {s a w : ℝ} (hs : 0 < s) (ha : 0 < a) :
    HasDerivAt (deriv (fun t : ℝ => rowPotential (s,a+t*w)))
      (phiDD (a/Real.sqrt s)*w^2/s^2) 0 := by
  have hsqrt := Real.sqrt_pos.mpr hs
  have ht : 0 < a/Real.sqrt s := div_pos ha hsqrt
  have hgap (t : ℝ) : HasDerivAt (fun t : ℝ => (a+t*w)/Real.sqrt s) (w/Real.sqrt s) t := by
    simpa using (((hasDerivAt_id t).mul_const w).const_add a).div_const (Real.sqrt s)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (a+t*w)/Real.sqrt s := by
    exact (by fun_prop : Continuous (fun t : ℝ => (a+t*w)/Real.sqrt s)).continuousAt.eventually
      (lt_mem_nhds (by simpa using ht))
  have heq : deriv (fun t : ℝ => rowPotential (s,a+t*w)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (1/s)*(phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s))) := by
    filter_upwards [hnear] with t ht'
    exact (((hasDerivAt_phi ht').comp t (hgap t)).const_mul (1/s)).deriv
  have hd := (((hasDerivAt_phiD ht).comp_of_eq 0 (hgap 0) (by simp)).const_mul (1/s))
    |>.mul_const (w/Real.sqrt s)
  simp only [Function.comp_apply] at hd
  have heqfun : (fun t => (1/s)*phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s)) =
      (fun t => (1/s)*(phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s))) := by funext t; ring
  rw [heqfun] at hd
  have hcoef : (1/s)*(phiDD (a/Real.sqrt s)*(w/Real.sqrt s))*(w/Real.sqrt s) =
      phiDD (a/Real.sqrt s)*w^2/s^2 := by
    field_simp
    rw [Real.sq_sqrt hs.le]
  rw [hcoef] at hd
  exact hd.congr_of_eventuallyEq heq

theorem row_potential_second {s a b w : ℝ} (hs : 0 < s) (ha : 0 < a) :
    HasDerivAt (deriv (fun t : ℝ => rowPotential (s-b*t^2,a+t*w)))
      ((phiDD (a/Real.sqrt s)*w^2-psi (a/Real.sqrt s)*b)/s^2) 0 := by
  have h := quadratic_scale_second (b := b) (w := w) (rowPotential_contDiffAt hs ha)
  rw [(fixed_scale_second (w := w) hs ha).deriv] at h
  have hpartial : deriv (fun r : ℝ => rowPotential (r,a)) s = psi (a/Real.sqrt s)/(2*s^2) :=
    (hasDerivAt_scaled_phi ha hs).deriv
  rw [hpartial] at h
  convert h using 1
  ring

noncomputable def residualScale {n : ℕ} (z : Fin n → ℝ) : ℝ := residual z-4

noncomputable def smoothPotential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, rowPotential (residualScale z, D-A.mulVec z i)

theorem residualScale_line {n : ℕ} (z v : Fin n → ℝ)
    (hv : (∑ j, z j*v j) = 0) (t : ℝ) :
    residualScale (fun j => z j+t*v j) = residualScale z-t^2*(∑ j, v j^2) := by
  have heq : (∑ j, (z j+t*v j)^2) =
      (∑ j, z j^2)+2*t*(∑ j, z j*v j)+t^2*(∑ j, v j^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold residualScale residual
  rw [heq, hv]
  ring

theorem mulVec_line {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (z v : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    A.mulVec (fun j => z j+t*v j) i = A.mulVec z i+t*A.mulVec v i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem second_deriv_finite_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (c : ι → ℝ) (hf : ∀ i, ContDiffAt ℝ 2 (f i) 0)
    (hd : ∀ i, HasDerivAt (deriv (f i)) (c i) 0) :
    HasDerivAt (deriv (fun t => ∑ i, f i t)) (∑ i, c i) 0 := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, ContDiffAt ℝ 2 (f i) t :=
    eventually_all.mpr (fun i => (hf i).eventually (by norm_num))
  have heq : deriv (fun t => ∑ i, f i t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ i, deriv (f i) t) := by
    filter_upwards [hnear] with t ht
    exact deriv_fun_sum (fun i _ => (ht i).differentiableAt (by norm_num))
  exact (HasDerivAt.fun_sum (fun i _ => hd i)).congr_of_eventuallyEq heq

/-- Lemma 3.5, with Euclidean squared norms written as sums of squares. -/
theorem lemma_3_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z v : Fin n → ℝ)
    (hs : 0 < residualScale z) (hg : ∀ i, 0 < D-A.mulVec z i)
    (hv : (∑ j, z j*v j) = 0) :
    residualScale z^2 * deriv (deriv (fun t : ℝ =>
      smoothPotential A D (fun j => z j+t*v j))) 0 =
      (∑ i, deriv (deriv phi) ((D-A.mulVec z i)/Real.sqrt (residualScale z)) *
        (A.mulVec v i)^2) -
      (∑ i, psi ((D-A.mulVec z i)/Real.sqrt (residualScale z))) * (∑ j, v j^2) := by
  let s := residualScale z
  let b := ∑ j, v j^2
  let a := fun i => D-A.mulVec z i
  let w := fun i => -(A.mulVec v i)
  let f := fun i (t : ℝ) => rowPotential (s-b*t^2,a i+t*w i)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := by
    intro i
    have h := rowPotential_contDiffAt hs (hg i)
    have hp : ContDiffAt ℝ 2 (fun t : ℝ => (s-b*t^2,a i+t*w i)) 0 := by fun_prop
    have hh : ContDiffAt ℝ 2 rowPotential (s-b*0^2,a i+0*w i) := by simpa [s,a] using h
    exact ContDiffAt.comp (g := rowPotential)
      (f := fun t : ℝ => (s-b*t^2,a i+t*w i)) 0 hh hp
  have hd := second_deriv_finite_sum f
    (fun i => (phiDD (a i/Real.sqrt s)*(w i)^2-psi (a i/Real.sqrt s)*b)/s^2)
    hf (fun i => row_potential_second hs (hg i))
  have hline : (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) =
      (fun t => ∑ i, f i t) := by
    funext t
    unfold smoothPotential
    apply Finset.sum_congr rfl
    intro i _
    rw [residualScale_line z v hv, mulVec_line]
    dsimp [f,s,b,a,w]
    congr 1
    ext <;> ring
  rw [hline, hd.deriv]
  have hdd (i : Fin m) : deriv (deriv phi) (a i/Real.sqrt s) = phiDD (a i/Real.sqrt s) :=
    second_deriv_phi (div_pos (hg i) (Real.sqrt_pos.mpr hs))
  change s^2*(∑ i, (phiDD (a i/Real.sqrt s)*(w i)^2-psi (a i/Real.sqrt s)*b)/s^2) =
    (∑ i, deriv (deriv phi) (a i/Real.sqrt s)*(A.mulVec v i)^2) -
      (∑ i, psi (a i/Real.sqrt s))*b
  simp_rw [hdd]
  rw [← Finset.sum_div, mul_div_cancel₀ _ (pow_ne_zero 2 hs.ne')]
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, w, neg_sq]

end Stoc393

end
/- END original module: Stoc393.SecondVariation -/

/- BEGIN original module: Stoc393.PotentialCompact -/
section

/-! The extended-real barrier, including its infinite boundary values, and compact minimization. -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

noncomputable def barrierDenom (s a : ℝ) : ℝ := s / 5 * Real.sinh (a^2/(3*s))

noncomputable def extendedPotential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) : ℝ≥0∞ :=
  if 0 < residualScale z then
    ∑ i, (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹
  else 0

def feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) : Set (Fin n → ℝ) :=
  {z | InCube z ∧ 0 ≤ residualScale z ∧ ∀ i, A.mulVec z i ≤ D}

theorem continuous_residualScale {n : ℕ} : Continuous (residualScale (n := n)) := by
  unfold residualScale residual
  fun_prop

theorem continuous_rowAction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous (fun z : Fin n → ℝ => A.mulVec z i) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem barrierDenom_pos {s a : ℝ} (hs : 0 < s) (ha : 0 < a) : 0 < barrierDenom s a := by
  unfold barrierDenom
  exact mul_pos (by positivity) (Real.sinh_pos_iff.mpr (by positivity))

theorem rowPotential_eq_inv_denom {s a : ℝ} (hs : 0 < s) :
    rowPotential (s,a) = (barrierDenom s a)⁻¹ := by
  unfold rowPotential phi barrierDenom
  dsimp
  rw [div_pow, Real.sq_sqrt hs.le]
  field_simp

theorem extendedPotential_eq_ofReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) :
    extendedPotential A D z = ENNReal.ofReal (smoothPotential A D z) := by
  unfold extendedPotential smoothPotential
  rw [ite_eq_left hs, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [rowPotential_eq_inv_denom hs, ENNReal.ofReal_inv_of_pos (barrierDenom_pos hs (hg i))]
  · intro i _
    rw [rowPotential_eq_inv_denom hs]
    exact (inv_pos.mpr (barrierDenom_pos hs (hg i))).le

theorem extendedPotential_continuousAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z) :
    ContinuousAt (extendedPotential A D) z := by
  have hden (i : Fin m) : ContinuousAt
      (fun y : Fin n → ℝ => barrierDenom (residualScale y) (D-A.mulVec y i)) z := by
    unfold barrierDenom
    exact (continuous_residualScale.continuousAt.div_const 5).mul
      (Real.continuous_sinh.continuousAt.comp
        (((continuous_const.sub (continuous_rowAction A i)).pow 2).continuousAt.div
          (continuous_const.mul continuous_residualScale).continuousAt (by positivity)))
  have hc : ContinuousAt (fun y => ∑ i,
      (ENNReal.ofReal (barrierDenom (residualScale y) (D-A.mulVec y i)))⁻¹) z := by
    apply tendsto_finsetSum
    intro i _
    exact (ENNReal.continuous_ofReal.continuousAt.comp (hden i)).inv
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_residualScale.continuousAt.eventually (lt_mem_nhds hs)] with y hy
  exact ite_eq_left hy

theorem extendedPotential_lowerSemicontinuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) : LowerSemicontinuous (extendedPotential A D) := by
  intro z
  by_cases hs : 0 < residualScale z
  · exact (extendedPotential_continuousAt A D z hs).lowerSemicontinuousAt
  · intro b hb
    simp [extendedPotential, hs] at hb

theorem feasibleSet_compact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) :
    IsCompact (feasibleSet A D) := by
  have hcube : IsCompact {z : Fin n → ℝ | InCube z} := by
    have hc := isCompact_pi_infinite (fun _ : Fin n =>
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
    simpa only [InCube, abs_le, mem_Icc] using hc
  have hclosed : IsClosed {z : Fin n → ℝ |
      0 ≤ residualScale z ∧ ∀ i, A.mulVec z i ≤ D} := by
    change IsClosed ({z : Fin n → ℝ | 0 ≤ residualScale z} ∩
      {z : Fin n → ℝ | ∀ i, A.mulVec z i ≤ D})
    apply (isClosed_le continuous_const continuous_residualScale).inter
    change IsClosed {z | ∀ i, A.mulVec z i ≤ D}
    rw [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (continuous_rowAction A i) continuous_const)
  exact hcube.inter_right hclosed

theorem zero_mem_feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hn : 4 ≤ n) (hD : 0 ≤ D) : (0 : Fin n → ℝ) ∈ feasibleSet A D := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp
  · simp only [residualScale, residual, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    exact_mod_cast (show 0 ≤ (n : ℤ)-4 by omega)
  · intro i
    simpa using hD

theorem extendedPotential_exists_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hn : 4 ≤ n) (hD : 0 ≤ D) :
    ∃ z ∈ feasibleSet A D, IsMinOn (extendedPotential A D) (feasibleSet A D) z := by
  exact LowerSemicontinuousOn.exists_isMinOn ⟨0, zero_mem_feasibleSet A D hn hD⟩
    (feasibleSet_compact A D) ((extendedPotential_lowerSemicontinuous A D).lowerSemicontinuousOn _)

theorem finite_extendedPotential_positive_gaps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (z : Fin n → ℝ)
    (hs : 0 < residualScale z) (hg : ∀ i, A.mulVec z i ≤ D)
    (hfinite : extendedPotential A D z < ∞) : ∀ i, 0 < D-A.mulVec z i := by
  intro i
  have hrow : (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹ < ∞ := by
    apply ENNReal.sum_lt_top.mp (show
      (∑ i, (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹) < ∞ from
      (by simpa [extendedPotential, hs] using hfinite)) i (Finset.mem_univ i)
  have hnonzero : D-A.mulVec z i ≠ 0 := by
    intro heq
    simp [heq, barrierDenom] at hrow
  exact lt_of_le_of_ne (sub_nonneg.mpr (hg i)) (Ne.symm hnonzero)

end Stoc393

end
/- END original module: Stoc393.PotentialCompact -/

/- BEGIN original module: Stoc393.FaceTrace -/
section

/-! Capped trace after imposing the single orthogonality constraint on a cube face. -/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

theorem face_capped_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (z : Fin n → ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (w : Fin m → ℝ) (L : ℝ) (hw : ∀ i, 0 ≤ w i) (hL : 0 < L)
    (hq : ∀ v : Fin n → ℝ, (∑ j, z j*v j) = 0 → (∀ j ∉ J, v j = 0) →
      L*(∑ j, v j^2) ≤ ∑ i, w i*(A.mulVec v i)^2) :
    (J.card : ℝ)-1 ≤ J.card/L*(∑ i, min (w i) (L/J.card)) := by
  classical
  let restrict (a : Fin n → ℝ) : EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => a j)
  let S : Submodule ℝ (EuclideanSpace ℝ J) := Submodule.span ℝ {restrict z}
  let W := Sᗮ
  have hSdim : finrank ℝ S ≤ 1 := by
    simpa [S] using! finrank_span_finset_le_card (R := ℝ) ({restrict z} : Finset (EuclideanSpace ℝ J))
  have hdim_sum : finrank ℝ S+finrank ℝ W = J.card := by
    simpa using S.finrank_add_finrank_orthogonal
  have hdim : (J.card : ℝ)-1 ≤ (finrank ℝ W : ℝ) := by
    have h : J.card ≤ 1+finrank ℝ W := by omega
    have h' : (J.card : ℝ) ≤ 1+(finrank ℝ W : ℝ) := by exact_mod_cast h
    linarith
  have ha (i : Fin m) : ‖restrict (A i)‖^2 ≤ (J.card : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j : J, (restrict (A i) j)^2) ≤ ∑ _j : J, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_abs_of_abs_le_one (hA i j)).trans (hA i j)
      _ = _ := by simp
  have hbound := capped_trace_subspace W (fun i => restrict (A i)) w J.card L
    hw (by exact_mod_cast hJ.card_pos) hL ha
  apply hdim.trans
  apply hbound
  intro u
  let v : Fin n → ℝ := fun j => if hj : j ∈ J then (u : EuclideanSpace ℝ J) ⟨j,hj⟩ else 0
  have hvout (j : Fin n) (hj : j ∉ J) : v j = 0 := by simp [v,hj]
  have hsum (a : Fin n → ℝ) :
      (∑ j, a j*v j) = inner ℝ (restrict a) (u : EuclideanSpace ℝ J) := by
    calc
      (∑ j, a j*v j) = ∑ j ∈ J, a j*v j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ J)
        intro j _ hj
        simp [hvout j hj]
      _ = ∑ j : J, a j*(u : EuclideanSpace ℝ J) j := by
        rw [← Finset.sum_coe_sort J]
        simp [v]
      _ = _ := by
        change (∑ j : J, a j*(u : EuclideanSpace ℝ J) j) =
          ∑ j : J, (u : EuclideanSpace ℝ J) j*a j
        apply Finset.sum_congr rfl
        intro j _
        ring
  have horth : (∑ j, z j*v j) = 0 := by
    rw [hsum]
    exact S.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_singleton (restrict z))) u.property
  have hnorm : (∑ j, v j^2) = ‖u‖^2 := by
    have h := hsum v
    have hrestrict : restrict v = (u : EuclideanSpace ℝ J) := by
      ext j
      simp [restrict,v]
    rw [hrestrict, real_inner_self_eq_norm_sq] at h
    simpa only [pow_two] using! h
  have h := hq v horth hvout
  simpa only [hnorm, Matrix.mulVec, dotProduct, hsum] using h

end Stoc393

end
/- END original module: Stoc393.FaceTrace -/

/- BEGIN original module: Stoc393.MinimizerGeometry -/
section

/-! Feasible variations on cube faces and the contradiction at an interior minimizer. -/

open scoped Topology BigOperators ENNReal
open Filter Set Module
set_option autoImplicit false

namespace Stoc393

noncomputable def activeCoords {n : ℕ} (z : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => |z j| < 1)

theorem residual_le_active_card {n : ℕ} {z : Fin n → ℝ} (hz : InCube z) :
    residual z ≤ ((activeCoords z).card : ℝ) := by
  classical
  have heq : residual z = ∑ j, (1-z j^2) := by
    simp [residual, Finset.sum_sub_distrib]
  rw [heq]
  calc
    ∑ j, (1-z j^2) ≤ ∑ j, if |z j| < 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · linarith [sq_nonneg (z j)]
      · have habs : |z j| = 1 := le_antisymm (hz j) (le_of_not_gt hj)
        have hsq : z j^2 = 1 := by nlinarith [sq_abs (z j)]
        simp [hsq]
    _ = _ := by simp [activeCoords]

theorem line_eventually_inCube {n : ℕ} {z : Fin n → ℝ} (hz : InCube z)
    (v : Fin n → ℝ) (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), InCube (fun j => z j+t*v j) := by
  apply eventually_all.mpr
  intro j
  by_cases hj : |z j| < 1
  · have hc : ContinuousAt (fun t : ℝ => |z j+t*v j|) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa using hj))).mono (fun _ ht => ht.le)
  · have hv : v j = 0 := hsupport j (by simpa [activeCoords] using hj)
    simpa [hv] using (Eventually.of_forall (fun _ : ℝ => hz j) :
      ∀ᶠ _t in 𝓝 (0 : ℝ), |z j| ≤ 1)

theorem line_eventually_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) {z : Fin n → ℝ} (hz : InCube z) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) (v : Fin n → ℝ)
    (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (fun j => z j+t*v j) ∈ feasibleSet A D ∧
      0 < residualScale (fun j => z j+t*v j) ∧
      ∀ i, 0 < D-A.mulVec (fun j => z j+t*v j) i := by
  have hsnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < residualScale (fun j => z j+t*v j) := by
    have hc := continuous_residualScale.comp
      (by fun_prop : Continuous (fun t : ℝ => fun j => z j+t*v j))
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hs))
  have hgnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < D-A.mulVec (fun j => z j+t*v j) i := by
    apply eventually_all.mpr
    intro i
    have hc := ((continuous_const (y := D)).sub (continuous_rowAction A i)).comp
      (by fun_prop : Continuous (fun t : ℝ => fun j => z j+t*v j))
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hg i))
  filter_upwards [line_eventually_inCube hz v hsupport, hsnear, hgnear] with t ht hs' hg'
  exact ⟨⟨ht, hs'.le, fun i => (sub_pos.mp (hg' i)).le⟩, hs', hg'⟩

theorem smoothPotential_contDiffAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) : ContDiffAt ℝ 2 (smoothPotential A D) z := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ 2 (fun y : Fin n → ℝ => (residualScale y,D-A.mulVec y i)) z := by
    unfold residualScale residual Matrix.mulVec dotProduct
    fun_prop
  exact ContDiffAt.comp (g := rowPotential)
    (f := fun y : Fin n → ℝ => (residualScale y,D-A.mulVec y i)) z
    (rowPotential_contDiffAt hs (hg i)) hp

theorem second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {a : ℝ}
    (hmin : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra h
  have hneg : deriv (deriv f) a < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hmin,hmax] with x h₁ h₂
    exact le_antisymm h₂ h₁
  have hh := heq.deriv.deriv_eq
  have hconst : deriv (fun _ : ℝ => f a) = fun _ => 0 := by
    funext t
    exact deriv_const t (f a)
  rw [hconst, deriv_const] at hh
  linarith

theorem minimizer_quadratic_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) {z : Fin n → ℝ} (hz : InCube z) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i)
    (hmin : IsMinOn (extendedPotential A D) (feasibleSet A D) z)
    (v : Fin n → ℝ) (horth : (∑ j, z j*v j) = 0)
    (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    (∑ i, psi ((D-A.mulVec z i)/Real.sqrt (residualScale z))) * (∑ j, v j^2) ≤
      ∑ i, deriv (deriv phi) ((D-A.mulVec z i)/Real.sqrt (residualScale z)) *
        (A.mulVec v i)^2 := by
  have hlocal : IsLocalMin (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) 0 := by
    filter_upwards [line_eventually_feasible A D hz hs hg v hsupport] with t ht
    have h := hmin ht.1
    change extendedPotential A D z ≤ extendedPotential A D (fun j => z j+t*v j) at h
    rw [extendedPotential_eq_ofReal A D z hs hg,
      extendedPotential_eq_ofReal A D _ ht.2.1 ht.2.2] at h
    have hnonneg : 0 ≤ smoothPotential A D (fun j => z j+t*v j) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (one_div_nonneg.mpr ht.2.1.le)
        (phi_pos (div_pos (ht.2.2 i) (Real.sqrt_pos.mpr ht.2.1))).le
    simpa using (ENNReal.ofReal_le_ofReal_iff hnonneg).mp h
  have hc : ContinuousAt (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) 0 := by
    have hh : ContinuousAt (smoothPotential A D) (fun j => z j+0*v j) := by
      simpa using (smoothPotential_contDiffAt A D z hs hg).continuousAt
    have hcomp := hh.comp (by fun_prop : ContinuousAt (fun t : ℝ => fun j => z j+t*v j) 0)
    exact hcomp
  have hsecond := second_deriv_nonneg_of_local_min hlocal hc
  have hidentity := lemma_3_5 A D z v hs hg horth
  nlinarith [mul_nonneg (sq_nonneg (residualScale z)) hsecond]

/-- A minimizer below level one must be on the residual-four boundary. -/
theorem minimizer_residualScale_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (hm : 0 < m) (D : ℝ) {z : Fin n → ℝ}
    (hz : z ∈ feasibleSet A D)
    (hmin : IsMinOn (extendedPotential A D) (feasibleSet A D) z)
    (hvalue : extendedPotential A D z < 1) : residualScale z = 0 := by
  classical
  by_contra hzero
  have hs : 0 < residualScale z := lt_of_le_of_ne hz.2.1 (Ne.symm hzero)
  have hg := finite_extendedPotential_positive_gaps A D z hs hz.2.2
    (hvalue.trans (by simp))
  have hpotential : smoothPotential A D z < 1 := by
    rw [extendedPotential_eq_ofReal A D z hs hg, ← ENNReal.ofReal_one] at hvalue
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hvalue
  let J := activeCoords z
  let t := fun i => (D-A.mulVec z i)/Real.sqrt (residualScale z)
  let w := fun i => deriv (deriv phi) (t i)
  let p := fun i => phi (t i)
  let q := fun i => psi (t i)
  let L := ∑ i, q i
  have ht (i : Fin m) : 0 < t i := div_pos (hg i) (Real.sqrt_pos.mpr hs)
  have hL : 0 < L := by
    let : NeZero m := ⟨by omega⟩
    exact Finset.sum_pos (fun i _ => psi_pos (ht i)) Finset.univ_nonempty
  have hres := residual_le_active_card hz.1
  have hJ : 0 < (J.card : ℝ) := by
    dsimp [residualScale] at hs
    dsimp [J]
    linarith
  have htrace := face_capped_trace A hA z J
    (Finset.card_pos.mp (by exact_mod_cast hJ)) w L
    (fun i => (second_deriv_phi_pos (ht i)).le) hL
    (fun v horth hsupport => minimizer_quadratic_form A D hz.1 hs hg hmin v horth hsupport)
  have hsum : (∑ i, p i) < (J.card : ℝ)-4 := by
    have hid : residualScale z*smoothPotential A D z = ∑ i, p i := by
      unfold smoothPotential rowPotential
      simp only [← Finset.mul_sum, p, t]
      field_simp
    have hh : (∑ i, p i) < residualScale z := by nlinarith
    exact hh.trans_le (sub_le_sub_right hres 4)
  exact dimension_contradiction w p q J.card L (J.card-1)
    hJ hL rfl le_rfl htrace
    (fun i => lemma_3_3_c (ht i) (div_pos hL hJ)) hsum

/-- Compact minimization and the interior contradiction give a residual-four point. -/
theorem exists_residual_four_point {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (hm : 0 < m) (D : ℝ) (hn : 4 ≤ n) (hD : 0 ≤ D)
    (hinitial : extendedPotential A D 0 < 1) :
    ∃ z ∈ feasibleSet A D, residual z = 4 := by
  obtain ⟨z,hz,hmin⟩ := extendedPotential_exists_min A D hn hD
  have hvalue : extendedPotential A D z < 1 :=
    (hmin (zero_mem_feasibleSet A D hn hD)).trans_lt hinitial
  have hzero := minimizer_residualScale_zero A hA hm D hz hmin hvalue
  exact ⟨z,hz,sub_eq_zero.mp hzero⟩

end Stoc393

end
/- END original module: Stoc393.MinimizerGeometry -/

/- BEGIN original module: Stoc393.UpperBound -/
section

/-! Proposition 3.6 and the full upper bound (Theorems 1.2 and 3.1). -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

noncomputable def discrepancyRadius (d n : ℕ) : ℝ :=
  Real.sqrt (3*(n : ℝ)*Real.arsinh (10*(d : ℝ)/(n : ℝ)))

def symmetricRows {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin (d+d)) (Fin n) ℝ := Fin.append (fun i j => A i j) (fun i j => -A i j)

theorem discrepancyRadius_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < discrepancyRadius d n := by
  unfold discrepancyRadius
  apply Real.sqrt_pos.mpr
  have ha : 0 < Real.arsinh (10*(d : ℝ)/(n : ℝ)) := Real.arsinh_pos_iff.mpr (by positivity)
  positivity

theorem symmetricRows_entryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) : EntryBounded (symmetricRows A) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro k
    change |Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) _ j| ≤ 1
    simpa only [Fin.append_left, Fin.append_right, abs_neg] using hA k j
  · intro k
    change |Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) _ j| ≤ 1
    simpa only [Fin.append_left, Fin.append_right, abs_neg] using hA k j

theorem symmetricRows_feasible_norm {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (D : ℝ) (hD : 0 ≤ D) {z : Fin n → ℝ} (hz : z ∈ feasibleSet (symmetricRows A) D) :
    ‖A.mulVec z‖ ≤ D := by
  apply (pi_norm_le_iff_of_nonneg hD).mpr
  intro i
  have hpos := hz.2.2 (Fin.castAdd d i)
  have hneg := hz.2.2 (Fin.natAdd d i)
  change (∑ j, Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) (Fin.castAdd d i) j*z j) ≤ D at hpos
  change (∑ j, Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) (Fin.natAdd d i) j*z j) ≤ D at hneg
  rw [Fin.append_left] at hpos
  rw [Fin.append_right] at hneg
  change |A.mulVec z i| ≤ D
  apply abs_le.mpr
  constructor
  · have hn : -(A.mulVec z i) ≤ D := by
      simpa only [symmetricRows, Matrix.mulVec, dotProduct, Fin.append_right, neg_mul, Finset.sum_neg_distrib] using hneg
    linarith
  · simpa only [symmetricRows, Matrix.mulVec, dotProduct, Fin.append_left] using hpos

theorem full_scale_potential_eq_one {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    ((d+d : ℕ) : ℝ)*((1/(n : ℝ))*phi (discrepancyRadius d n/Real.sqrt n)) = 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ha : 0 < Real.arsinh (10*(d : ℝ)/(n : ℝ)) := Real.arsinh_pos_iff.mpr (by positivity)
  have hid : (discrepancyRadius d n/Real.sqrt n)^2/3 =
      Real.arsinh (10*(d : ℝ)/(n : ℝ)) := by
    unfold discrepancyRadius
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le]
    field_simp
  unfold phi
  rw [hid, Real.sinh_arsinh]
  push_cast
  field_simp
  ring

theorem initial_potential_lt_one {d n : ℕ} (A : Matrix (Fin (d+d)) (Fin n) ℝ)
    (hd : 0 < d) (hn : 4 < n) :
    extendedPotential A (discrepancyRadius d n) 0 < 1 := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < residualScale (0 : Fin n → ℝ) := by
    simpa [residualScale,residual] using sub_pos.mpr hnR
  have hD := discrepancyRadius_pos hd (by omega : 0 < n)
  have hg (i : Fin (d+d)) : 0 < discrepancyRadius d n-A.mulVec 0 i := by simpa using hD
  rw [extendedPotential_eq_ofReal A (discrepancyRadius d n) 0 hs hg, ← ENNReal.ofReal_one]
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
  have hmono := scaled_phi_strictMonoOn hD
    (show (n : ℝ)-4 ∈ Ioi 0 from sub_pos.mpr hnR)
    (show (n : ℝ) ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
    (show (n : ℝ)-4 < n by linarith)
  have hmult := mul_lt_mul_of_pos_left hmono (show (0 : ℝ) < ((d+d : ℕ) : ℝ) by positivity)
  rw [full_scale_potential_eq_one hd (by omega)] at hmult
  simpa [smoothPotential,rowPotential,residualScale,residual] using hmult

/-- Proposition 3.6 for the doubled-row formulation used in the paper. -/
theorem proposition_3_6 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) (hd : 0 < d) (hn : 4 < n) :
    (∃ z ∈ feasibleSet (symmetricRows A) (discrepancyRadius d n),
      IsMinOn (extendedPotential (symmetricRows A) (discrepancyRadius d n))
        (feasibleSet (symmetricRows A) (discrepancyRadius d n)) z ∧
      extendedPotential (symmetricRows A) (discrepancyRadius d n) z < ∞) ∧
    ∀ z ∈ feasibleSet (symmetricRows A) (discrepancyRadius d n),
      IsMinOn (extendedPotential (symmetricRows A) (discrepancyRadius d n))
        (feasibleSet (symmetricRows A) (discrepancyRadius d n)) z →
      ‖A.mulVec z‖ ≤ discrepancyRadius d n ∧ residual z = 4 := by
  have hD := (discrepancyRadius_pos hd (by omega : 0 < n)).le
  have hinitial := initial_potential_lt_one (symmetricRows A) hd hn
  have hzero := zero_mem_feasibleSet (symmetricRows A) (discrepancyRadius d n) (by omega) hD
  have hval (z : Fin n → ℝ)
      (hmin : IsMinOn (extendedPotential (symmetricRows A) (discrepancyRadius d n))
        (feasibleSet (symmetricRows A) (discrepancyRadius d n)) z) :
      extendedPotential (symmetricRows A) (discrepancyRadius d n) z < 1 :=
    (hmin hzero).trans_lt hinitial
  constructor
  · obtain ⟨z,hz,hmin⟩ := extendedPotential_exists_min (symmetricRows A)
      (discrepancyRadius d n) (by omega) hD
    exact ⟨z,hz,hmin,(hval z hmin).trans (by simp)⟩
  · intro z hz hmin
    refine ⟨symmetricRows_feasible_norm A _ hD hz, ?_⟩
    exact sub_eq_zero.mp (minimizer_residualScale_zero (symmetricRows A)
      (symmetricRows_entryBounded A hA) (by omega) _ hz hmin (hval z hmin))

/-- Theorem 1.2 (restated as Theorem 3.1), including all zero/small dimensions. -/
theorem upperBoundClaim_proof : UpperBoundClaim := by
  intro d n A hA
  by_cases hn : n ≤ 4
  · exact upper_bound_small_dimension A hA hn
  by_cases hd : d = 0
  · subst d
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    have hnorm : ‖A.mulVec (fun _ => 1)‖ = 0 := by simp
    rw [hnorm]
    unfold upperThreshold
    positivity
  have hdpos : 0 < d := by omega
  have hnpos : 4 < n := by omega
  obtain ⟨hexists,hall⟩ := proposition_3_6 A hA hdpos hnpos
  obtain ⟨z,hz,hmin,_⟩ := hexists
  obtain ⟨hrow,hres⟩ := hall z hz hmin
  exact signing_of_fractional_point hA hz.1 hrow hres.le

theorem theorem_3_1 : UpperBoundClaim := upperBoundClaim_proof

end Stoc393

end
/- END original module: Stoc393.UpperBound -/

/- BEGIN original module: Stoc393.UpperCorollaries -/
section

/-! Discrepancy, the square-matrix bound, and its explicit numerical constants. -/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

noncomputable def discrepancy {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).inf' Finset.univ_nonempty
    (fun b => ‖A.mulVec (fun j => bitSign (b j))‖)

noncomputable def extremalDiscrepancy (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ, EntryBounded A ∧ r = discrepancy A/Real.sqrt n}

noncomputable def signExtremalDiscrepancy (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, A i j = 1 ∨ A i j = -1) ∧ r = discrepancy A/Real.sqrt n}

theorem discrepancy_le_iff {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (B : ℝ) :
    discrepancy A ≤ B ↔ ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ B := by
  unfold discrepancy
  rw [Finset.inf'_le_iff]
  constructor
  · rintro ⟨b,_,hb⟩
    exact ⟨fun j => bitSign (b j), fun j => bitSign_isSign (b j), hb⟩
  · rintro ⟨x,hx,hbound⟩
    obtain ⟨b,rfl⟩ := (signings_iff_boolean x).mp hx
    exact ⟨b,Finset.mem_univ _,hbound⟩

theorem discrepancy_nonneg {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    0 ≤ discrepancy A := by
  exact Finset.le_inf' _ _ (fun _ _ => norm_nonneg _)

theorem discrepancy_upper_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) : discrepancy A ≤ upperThreshold d n :=
  (discrepancy_le_iff A _).mpr (upperBoundClaim_proof d n A hA)

theorem square_radius {n : ℕ} (hn : 0 < n) :
    discrepancyRadius n n = Real.sqrt (3*Real.arsinh 10)*Real.sqrt n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold discrepancyRadius
  rw [mul_div_cancel_right₀ _ hnR]
  rw [show 3*(n : ℝ)*Real.arsinh 10 = (3*Real.arsinh 10)*n by ring,
    Real.sqrt_mul (by have h := Real.arsinh_pos_iff.mpr (show (0 : ℝ) < 10 by norm_num); positivity)]

theorem square_matrix_normalized_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : EntryBounded A) :
    discrepancy A/Real.sqrt n ≤ Real.sqrt (3*Real.arsinh 10)+4/Real.sqrt n := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := discrepancy_upper_bound A hA
  change discrepancy A ≤ discrepancyRadius n n+4 at h
  rw [square_radius hn] at h
  apply (div_le_iff₀ hs).mpr
  calc
    discrepancy A ≤ Real.sqrt (3*Real.arsinh 10)*Real.sqrt n+4 := h
    _ = (Real.sqrt (3*Real.arsinh 10)+4/Real.sqrt n)*Real.sqrt n := by field_simp

theorem extremalDiscrepancy_upper_bound {n : ℕ} (hn : 0 < n) :
    extremalDiscrepancy n ≤ Real.sqrt (3*Real.arsinh 10)+4/Real.sqrt n := by
  apply csSup_le
  · exact ⟨discrepancy (0 : Matrix (Fin n) (Fin n) ℝ)/Real.sqrt n,
      0, (by intro i j; simp), rfl⟩
  · rintro r ⟨A,hA,rfl⟩
    exact square_matrix_normalized_bound hn A hA

/-- The decimal 2.9992 in the abstract, proved with an exact Taylor lower bound. -/
theorem scalar_constant_lt_decimal : Real.sqrt (3*Real.arsinh 10) < 3749/1250 := by
  let u : ℝ := (3749/1250)^2/3
  have he := Real.sum_le_exp_of_nonneg (x := u) (by norm_num [u]) 16
  have he' : (401 : ℝ)/20 < Real.exp u := by
    norm_num [u, Finset.sum_range_succ, Nat.factorial] at he
    linarith
  have hinv : Real.exp (-u) < 20/401 := by
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos u) (by norm_num)).mpr (by linarith)
  have hsinh : (10 : ℝ) < Real.sinh u := by
    rw [Real.sinh_eq]
    linarith
  have hasinh : Real.arsinh 10 < u := by
    apply Real.sinh_lt_sinh.mp
    simpa only [Real.sinh_arsinh] using hsinh
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3749/1250)).mpr
  dsimp [u] at hasinh
  linarith

/-- The numerical consequence stated after Theorem 1.2. -/
theorem extremalDiscrepancy_lt_three {n : ℕ} (hn : 10^8 ≤ n) :
    extremalDiscrepancy n < 3 := by
  have hnpos : 0 < n := by omega
  have hs : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact hn)
  have hdiv : (4 : ℝ)/Real.sqrt n ≤ 4/10000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h := extremalDiscrepancy_upper_bound hnpos
  have hc := scalar_constant_lt_decimal
  linarith

end Stoc393

end
/- END original module: Stoc393.UpperCorollaries -/

/- BEGIN original module: Stoc393.LowerAlgebra -/
section

/-! Deterministic identities used in Section 2 and Appendix B.
These do not prove any concentration or binomial-tail estimate.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

/-- Orthogonal columns give the energy identity for every real vector. -/
theorem orthogonal_columns_energy {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (scale : ℝ)
    (hH : ∀ j k, (∑ i, H i j * H i k) = if j = k then scale else 0)
    (x : Fin n → ℝ) :
    (∑ i, (H.mulVec x i) ^ 2) = scale * ∑ j, x j ^ 2 := by
  classical
  have hexpand (i : Fin m) : (H.mulVec x i) ^ 2 =
      ∑ j, ∑ k, (x j * x k) * (H i j * H i k) := by
    simp only [Matrix.mulVec, dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, ∑ k, (x j * x k) * (H i j * H i k)) =
        ∑ j, ∑ k, (x j * x k) * (∑ i, H i j * H i k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ j, (x j * x j) * scale := by simp [hH]
    _ = scale * ∑ j, x j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem orthogonal_columns_signing_energy {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (scale : ℝ)
    (hH : ∀ j k, (∑ i, H i j * H i k) = if j = k then scale else 0)
    {x : Fin n → ℝ} (hx : IsSigning x) :
    (∑ i, (H.mulVec x i) ^ 2) = scale * n := by
  rw [orthogonal_columns_energy H scale hH]
  have hx2 (j : Fin n) : x j ^ 2 = 1 := by
    rcases hx j with hj | hj <;> norm_num [hj]
  simp [hx2]

/-- The first deterministic inequality in Appendix B(b), with a general threshold. -/
theorem energy_above_threshold {ι : Type*} [Fintype ι] (z : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    (∑ i, z i ^ 2) - a * (∑ i, |z i|) ≤
      ∑ i ∈ Finset.univ.filter (fun i => a < |z i|), (z i ^ 2 - a ^ 2) := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have hmul := mul_le_mul_of_nonneg_left hi.le ha
    nlinarith
  · have hi' : |z i| ≤ a := le_of_not_gt hi
    have hmul := mul_le_mul_of_nonneg_left hi' (abs_nonneg (z i))
    nlinarith [sq_abs (z i)]

/-- A deterministic excess-energy consequence of small l1 norm, used before
the random-tail estimates. All parameters are real, so there are no rounding
or integer-division conventions hidden in this identity. -/
theorem excess_energy_from_l1 {ι : Type*} [Fintype ι] (z : ι → ℝ)
    {a N δ η : ℝ} (ha : 0 ≤ a) (ha2 : a ^ 2 = N)
    (henergy : (∑ i, z i ^ 2) = (1 - δ) * N ^ 2)
    (hl1 : (∑ i, |z i|) ≤ (1 - η) * N * a) :
    (η - δ) * N ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => a < |z i|), (z i ^ 2 - N) := by
  have h := energy_above_threshold z ha
  have hl := mul_le_mul_of_nonneg_left hl1 ha
  rw [henergy, ha2] at h
  have hid : a * ((1 - η) * N * a) = (1 - η) * N ^ 2 := by
    calc
      a * ((1 - η) * N * a) = (1 - η) * N * a ^ 2 := by ring
      _ = (1 - η) * N ^ 2 := by rw [ha2]; ring
  rw [hid] at hl
  nlinarith

end Stoc393

end
/- END original module: Stoc393.LowerAlgebra -/

/- BEGIN original module: Stoc393.FiniteProbability -/
section

/-! Exact uniform expectations and probabilities on finite sample spaces. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x)/(Fintype.card Ω : ℝ)

noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ)/(Fintype.card Ω : ℝ)

theorem uniformMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)

theorem uniformMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

theorem uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformMean (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformMean, hn]

theorem uniformProb_eq_indicator_mean {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    uniformProb P = uniformMean (fun x => if P x then 1 else 0) := by
  classical
  simp only [uniformProb,uniformMean, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  congr 1
  ext x
  simp

theorem uniformProb_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : 0 ≤ uniformProb P := by
  unfold uniformProb
  positivity

theorem uniformProb_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    uniformProb P ≤ 1 := by
  classical
  calc
    uniformProb P = uniformMean (fun x => if P x then 1 else 0) := uniformProb_eq_indicator_mean P
    _ ≤ uniformMean (fun _ : Ω => 1) := by
      apply uniformMean_mono
      intro x
      split_ifs <;> norm_num
    _ = 1 := uniformMean_const 1

theorem uniform_markov {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 < a) : uniformProb (fun x => a ≤ f x) ≤ uniformMean f/a := by
  classical
  rw [le_div_iff₀ ha, uniformProb_eq_indicator_mean]
  have hm : uniformMean (fun x => if a ≤ f x then a else 0) ≤ uniformMean f := by
    apply uniformMean_mono
    intro x
    split_ifs with hx
    · exact hx
    · exact hf x
  convert hm using 1
  unfold uniformMean
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change (if a ≤ f x then (1 : ℝ) else 0)*a = (if a ≤ f x then a else 0)
  split_ifs <;> simp

theorem uniformMean_bool_product {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    uniformMean (fun b : ι → Bool => ∏ i, f i (b i)) =
      ∏ i, (f i true+f i false)/2 := by
  classical
  unfold uniformMean
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

noncomputable def rademacherSum {k : ℕ} (b : Fin k → Bool) : ℝ := ∑ j, bitSign (b j)

theorem rademacher_mgf (k : ℕ) (t : ℝ) :
    uniformMean (fun b : Fin k → Bool => Real.exp (t*rademacherSum b)) = Real.cosh t^k := by
  have hid (b : Fin k → Bool) : Real.exp (t*rademacherSum b) =
      ∏ j, Real.exp (t*bitSign (b j)) := by
    unfold rademacherSum
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hid]
  rw [uniformMean_bool_product (fun (_ : Fin k) b => Real.exp (t*bitSign b))]
  simp [bitSign,Real.cosh_eq,div_pow]

theorem rademacher_mgf_le (k : ℕ) (t : ℝ) :
    uniformMean (fun b : Fin k → Bool => Real.exp (t*rademacherSum b)) ≤
      Real.exp ((k : ℝ)*t^2/2) := by
  rw [rademacher_mgf, show (k : ℝ)*t^2/2 = k*(t^2/2) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.cosh_pos t).le (Real.cosh_le_exp_half_sq t) k

/-- Lemma 2.2(b), in fact for every positive number of signs. -/
theorem lemma_2_2_b {k : ℕ} (hk : 0 < k) (t : ℝ) :
    uniformMean (fun b : Fin k → Bool => Real.exp (t*rademacherSum b/Real.sqrt k)) ≤
      Real.exp (t^2/2) := by
  have h := rademacher_mgf_le k (t/Real.sqrt k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hid : (k : ℝ)*(t/Real.sqrt k)^2/2 = t^2/2 := by
    rw [div_pow, Real.sq_sqrt hkR.le]
    field_simp
  rw [hid] at h
  simpa only [div_mul_eq_mul_div] using h

theorem uniformMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : uniformMean (fun x => f (e x)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformProb_mono {Ω : Type*} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ x, P x → Q x) : uniformProb P ≤ uniformProb Q := by
  classical
  rw [uniformProb_eq_indicator_mean, uniformProb_eq_indicator_mean]
  apply uniformMean_mono
  intro x
  by_cases hp : P x
  · simp [hp,h x hp]
  · simp only [ite_eq_right hp]
    split_ifs <;> norm_num

theorem uniformProb_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (P : Ω' → Prop) : uniformProb (fun x => P (e x)) = uniformProb P := by
  classical
  rw [uniformProb_eq_indicator_mean, uniformProb_eq_indicator_mean]
  exact uniformMean_equiv e (fun x => if P x then 1 else 0)

theorem uniformMean_pi_product {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (f : ι → β → ℝ) :
    uniformMean (fun b : ι → β => ∏ i, f i (b i)) = ∏ i, uniformMean (f i) := by
  unfold uniformMean
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun, Nat.cast_pow, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]

theorem rademacher_normalized_upper_tail {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) :
    uniformProb (fun b : Fin k → Bool => a ≤ rademacherSum b/Real.sqrt k) ≤
      Real.exp (-a^2/2) := by
  have hmono := uniformProb_mono (P := fun b : Fin k → Bool => a ≤ rademacherSum b/Real.sqrt k)
    (Q := fun b : Fin k → Bool => Real.exp (a^2) ≤ Real.exp (a*rademacherSum b/Real.sqrt k))
    (fun b hb => Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left hb ha
      simpa only [pow_two, mul_div_assoc] using h))
  have hmarkov := uniform_markov (f := fun b : Fin k → Bool => Real.exp (a*rademacherSum b/Real.sqrt k))
    (fun _ => Real.exp_nonneg _) (Real.exp_pos (a^2))
  have hmgf := div_le_div_of_nonneg_right (lemma_2_2_b hk a) (Real.exp_nonneg (a^2))
  have h := hmono.trans (hmarkov.trans hmgf)
  rw [← Real.exp_sub] at h
  convert h using 1
  congr 1
  ring

theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

def negateBits (k : ℕ) : (Fin k → Bool) ≃ (Fin k → Bool) where
  toFun b j := !(b j)
  invFun b j := !(b j)
  left_inv b := by funext j; simp
  right_inv b := by funext j; simp

theorem rademacherSum_negate (k : ℕ) (b : Fin k → Bool) :
    rademacherSum (negateBits k b) = -rademacherSum b := by
  simp [rademacherSum, negateBits, bitSign_not, Finset.sum_neg_distrib]

theorem rademacher_normalized_lower_tail {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) :
    uniformProb (fun b : Fin k → Bool => rademacherSum b/Real.sqrt k ≤ -a) ≤
      Real.exp (-a^2/2) := by
  have h := uniformProb_equiv (negateBits k)
    (fun b : Fin k → Bool => a ≤ rademacherSum b/Real.sqrt k)
  have heq : (fun b : Fin k → Bool => a ≤ rademacherSum (negateBits k b)/Real.sqrt k) =
      (fun b : Fin k → Bool => rademacherSum b/Real.sqrt k ≤ -a) := by
    funext b
    rw [rademacherSum_negate, neg_div, le_neg]
  rw [heq] at h
  rw [h]
  exact rademacher_normalized_upper_tail hk ha

theorem uniformMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun x => f x+g x) = uniformMean f+uniformMean g := by
  simp [uniformMean,Finset.sum_add_distrib,add_div]

theorem uniformMean_const_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun x => a*f x) = a*uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum, mul_div_assoc]

theorem uniformMean_exp_shift {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    uniformMean (fun x => Real.exp (f x-a)) = uniformMean (fun x => Real.exp (f x))/Real.exp a := by
  simp only [Real.exp_sub, uniformMean, ← Finset.sum_div]
  ring

/-- Finite Holder interpolation, expressed directly in exponential moments. -/
theorem uniformMean_exp_mixing {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ)
    {a b l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hf : uniformMean (fun x => Real.exp (f x)) ≤ Real.exp a)
    (hg : uniformMean (fun x => Real.exp (g x)) ≤ Real.exp b) :
    uniformMean (fun x => Real.exp ((1-l)*f x+l*g x)) ≤ Real.exp ((1-l)*a+l*b) := by
  have hpoint (x : Ω) : Real.exp ((1-l)*(f x-a)+l*(g x-b)) ≤
      (1-l)*Real.exp (f x-a)+l*Real.exp (g x-b) := by
    simpa only [smul_eq_mul] using convexOn_exp.2 (Set.mem_univ (f x-a))
      (Set.mem_univ (g x-b)) (by linarith : 0 ≤ 1-l) hl0 (by ring : 1-l+l = 1)
  have h := uniformMean_mono hpoint
  rw [uniformMean_add, uniformMean_const_mul, uniformMean_const_mul,
    uniformMean_exp_shift, uniformMean_exp_shift] at h
  have hf' : uniformMean (fun x => Real.exp (f x))/Real.exp a ≤ 1 :=
    (div_le_one (Real.exp_pos a)).mpr hf
  have hg' : uniformMean (fun x => Real.exp (g x))/Real.exp b ≤ 1 :=
    (div_le_one (Real.exp_pos b)).mpr hg
  have hnormalized : uniformMean (fun x => Real.exp ((1-l)*(f x-a)+l*(g x-b))) ≤ 1 := by
    have hfa := mul_le_mul_of_nonneg_left hf' (show 0 ≤ 1-l by linarith)
    have hgb := mul_le_mul_of_nonneg_left hg' hl0
    linarith
  have hfactor (x : Ω) : Real.exp ((1-l)*f x+l*g x) =
      Real.exp ((1-l)*a+l*b)*Real.exp ((1-l)*(f x-a)+l*(g x-b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [uniformMean_const_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormalized (Real.exp_nonneg _)

end Stoc393

end
/- END original module: Stoc393.FiniteProbability -/

/- BEGIN original module: Stoc393.TalagrandScalar -/
section

/-! Scalar mixing estimate for the dimension induction in Talagrand's inequality.
The induction implemented in `Talagrand.lean` follows the convex-set proof in Tao's 2009 exposition:
https://terrytao.wordpress.com/2009/06/09/talagrands-concentration-inequality/.
This file proves only its scalar ingredient, not the concentration theorem.
-/
open Set
set_option autoImplicit false
namespace Stoc393

noncomputable def talagrandLogGap (q : ℝ) : ℝ :=
  Real.log (1+q)+(1-2*q)*Real.log (1-q)-q^2

theorem hasDerivAt_talagrandLogGap {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1/2)) :
    HasDerivAt talagrandLogGap
      (1/(1+q)-2*Real.log (1-q)-(1-2*q)/(1-q)-2*q) q := by
  have hplus : 1+q ≠ 0 := by linarith [hq.1]
  have hminus : 1-q ≠ 0 := by linarith [hq.2]
  have h := (((hasDerivAt_id q).const_add 1).log hplus).add
    ((((hasDerivAt_id q).const_mul 2).const_sub 1).mul
      (((hasDerivAt_id q).const_sub 1).log hminus)) |>.sub ((hasDerivAt_id q).pow 2)
  convert h using 1
  · rfl
  · dsimp
    ring

theorem talagrand_log_mixing {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1/2)) :
    q^2-(1-2*q)*Real.log (1-q) ≤ Real.log (1+q) := by
  have hmono : MonotoneOn talagrandLogGap (Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_talagrandLogGap hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_talagrandLogGap (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) (1/2) := interior_subset hx
      have hp : 0 < 1+x := by linarith [hx'.1]
      have hm : 0 < 1-x := by linarith [hx'.2]
      have hden : 0 < 1-x^2 := by nlinarith [hx'.1,hx'.2]
      have hlog := Real.log_le_sub_one_of_pos hm
      have hid : 1/(1+x)-2*Real.log (1-x)-(1-2*x)/(1-x)-2*x =
          2*x^2/(1-x^2)-2*(Real.log (1-x)+x) := by
        field_simp
        ring
      rw [hid]
      have hnonneg : 0 ≤ 2*x^2/(1-x^2) := by positivity
      linarith
  have h := hmono (show (0 : ℝ) ∈ Icc 0 (1/2) by norm_num) hq hq.1
  simpa [talagrandLogGap] using h

theorem talagrand_exp_mixing {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1/2)) :
    Real.exp (q^2-(1-2*q)*Real.log (1-q)) ≤ 1+q := by
  simpa only [Real.exp_log (by linarith [hq.1] : 0 < 1+q)] using
    Real.exp_le_exp.mpr (talagrand_log_mixing hq)

theorem exp_quarter_le_four_thirds : Real.exp (1/4 : ℝ) ≤ 4/3 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-1/4 : ℝ))
    (Real.exp_nonneg (1/4 : ℝ))
  have hid : Real.exp (-1/4 : ℝ)*Real.exp (1/4 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at h
  linarith

/-- A concrete mixing coefficient, including zero-probability slices. -/
theorem talagrand_scalar_mixing {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ l ∈ Icc (0 : ℝ) 1,
      Real.exp (l^2/4-(1-l)*Real.log r) ≤ 2-r := by
  by_cases hr : 1/2 ≤ r
  · refine ⟨2*(1-r), ⟨by linarith, by linarith⟩, ?_⟩
    have h := talagrand_exp_mixing (q := 1-r) ⟨by linarith, by linarith⟩
    rw [show (2*(1-r))^2/4 = (1-r)^2 by ring]
    simpa only [show 1-(1-r) = r by ring, show 1+(1-r) = 2-r by ring] using h
  · refine ⟨1, by norm_num, ?_⟩
    have h := exp_quarter_le_four_thirds
    simp only [one_pow, sub_self, zero_mul, sub_zero]
    linarith

/-- The scalar estimate used after averaging the two coordinate slices. -/
theorem talagrand_scalar_average {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ l ∈ Icc (0 : ℝ) 1,
      (1+r)/4*(1+Real.exp (l^2/4-(1-l)*Real.log r)) ≤ 1 := by
  obtain ⟨l,hl,hbound⟩ := talagrand_scalar_mixing hr0 hr1
  refine ⟨l,hl,?_⟩
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (1+r)/4 by positivity)
  nlinarith [sq_nonneg (1-r)]

end Stoc393

end
/- END original module: Stoc393.TalagrandScalar -/

/- BEGIN original module: Stoc393.TalagrandGeometry -/
section

/-! Euclidean coordinate slices for the convex-set concentration induction. -/
open scoped BigOperators
open Set
set_option autoImplicit false
namespace Stoc393

noncomputable def prependPoint {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (Fin.cons c (fun j => x j))

noncomputable def cubePoint {n : ℕ} (b : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => bitSign (b j))

noncomputable def coordinateSlice {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := prependPoint c ⁻¹' K

theorem prependPoint_affine {n : ℕ} (c a b : ℝ) (hab : a+b = 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    prependPoint c (a • x+b • y) = a • prependPoint c x+b • prependPoint c y := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change c = a*c+b*c
    rw [← add_mul,hab,one_mul]
  · simp [prependPoint]

theorem continuous_prependPoint {n : ℕ} (c : ℝ) :
    Continuous (prependPoint (n := n) c) := by
  unfold prependPoint
  fun_prop

theorem coordinateSlice_closed {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hK : IsClosed K) (c : ℝ) : IsClosed (coordinateSlice K c) :=
  hK.preimage (continuous_prependPoint c)

theorem coordinateSlice_convex {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hK : Convex ℝ K) (c : ℝ) : Convex ℝ (coordinateSlice K c) := by
  intro x hx y hy a b ha hb hab
  change prependPoint c (a • x+b • y) ∈ K
  rw [prependPoint_affine c a b hab]
  exact hK hx hy ha hb hab

theorem prependPoint_dist_sq {n : ℕ} (c d : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (prependPoint c x) (prependPoint d y)^2 = (c-d)^2+dist x y^2 := by
  simp only [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  rw [Fin.sum_univ_succ]
  simp [prependPoint]

theorem cubePoint_cons {n : ℕ} (b : Bool) (bs : Fin n → Bool) :
    cubePoint (Fin.cons b bs) = prependPoint (bitSign b) (cubePoint bs) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [cubePoint,prependPoint]

theorem prependPoint_mix {n : ℕ} (c d a b : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    prependPoint (a*c+b*d) (a • x+b • y) = a • prependPoint c x+b • prependPoint d y := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [prependPoint]

theorem euclidean_dist_sq_convex {n : ℕ} (x y z : EuclideanSpace ℝ (Fin n))
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    dist x ((1-l) • y+l • z)^2 ≤ (1-l)*dist x y^2+l*dist x z^2 := by
  simp only [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hl1) hl0) (sq_nonneg (y j-z j))
  nlinarith

theorem slice_infDist_bound {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hK : IsClosed K) (c d : ℝ) (hne : (coordinateSlice K d).Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) :
    Metric.infDist (prependPoint c x) K^2 ≤ (c-d)^2+Metric.infDist x (coordinateSlice K d)^2 := by
  obtain ⟨y,hy,hdist⟩ := (coordinateSlice_closed hK d).exists_infDist_eq_dist hne x
  have h := Metric.infDist_le_dist_of_mem (x := prependPoint c x) (show prependPoint d y ∈ K from hy)
  have hsquare := (sq_le_sq₀ Metric.infDist_nonneg dist_nonneg).mpr h
  rw [prependPoint_dist_sq, ← hdist] at hsquare
  exact hsquare

theorem slice_infDist_mixing {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (c d : ℝ)
    (hne_c : (coordinateSlice K c).Nonempty) (hne_d : (coordinateSlice K d).Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Metric.infDist (prependPoint c x) K^2 ≤ l^2*(c-d)^2+
      (1-l)*Metric.infDist x (coordinateSlice K c)^2+l*Metric.infDist x (coordinateSlice K d)^2 := by
  obtain ⟨y,hy,hdy⟩ := (coordinateSlice_closed hclosed c).exists_infDist_eq_dist hne_c x
  obtain ⟨z,hz,hdz⟩ := (coordinateSlice_closed hclosed d).exists_infDist_eq_dist hne_d x
  have hmem := hconvex (show prependPoint c y ∈ K from hy)
    (show prependPoint d z ∈ K from hz) (show 0 ≤ 1-l by linarith) hl0 (by ring : 1-l+l = 1)
  rw [← prependPoint_mix] at hmem
  have hdist := Metric.infDist_le_dist_of_mem (x := prependPoint c x) hmem
  have hsquare := (sq_le_sq₀ Metric.infDist_nonneg dist_nonneg).mpr hdist
  rw [prependPoint_dist_sq] at hsquare
  have hconv := euclidean_dist_sq_convex x y z hl0 hl1
  rw [← hdy, ← hdz] at hconv
  have halgebra : (c-((1-l)*c+l*d))^2 = l^2*(c-d)^2 := by ring
  rw [halgebra] at hsquare
  linarith

end Stoc393

end
/- END original module: Stoc393.TalagrandGeometry -/

/- BEGIN original module: Stoc393.CubeProbability -/
section

/-! Splitting the uniform discrete cube into its two first-coordinate slices. -/
open scoped BigOperators
open Set
set_option autoImplicit false
namespace Stoc393

def consBitsEquiv (n : ℕ) : (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun b := (b 0, fun j => b j.succ)
  left_inv p := by cases p; rfl
  right_inv b := by ext j; exact Fin.cases rfl (fun _ => rfl) j

theorem uniformMean_cons {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    uniformMean f = (uniformMean (fun b => f (Fin.cons true b))+
      uniformMean (fun b => f (Fin.cons false b)))/2 := by
  rw [← uniformMean_equiv (consBitsEquiv n) f]
  simp only [uniformMean, consBitsEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem uniformProb_cons {n : ℕ} (P : (Fin (n+1) → Bool) → Prop) :
    uniformProb P = (uniformProb (fun b => P (Fin.cons true b))+
      uniformProb (fun b => P (Fin.cons false b)))/2 := by
  classical
  simp only [uniformProb_eq_indicator_mean]
  exact uniformMean_cons (fun b => if P b then 1 else 0)

theorem uniformProb_pos_iff {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    0 < uniformProb P ↔ ∃ x, P x := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  unfold uniformProb
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]
  simp only [Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def cubeProbability {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  uniformProb (fun b : Fin n → Bool => cubePoint b ∈ K)

noncomputable def cubeDistanceMoment {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  uniformMean (fun b : Fin n → Bool => Real.exp (Metric.infDist (cubePoint b) K^2/16))

noncomputable def sliceDistanceMoment {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (c : ℝ) : ℝ :=
  uniformMean (fun b : Fin n → Bool => Real.exp (Metric.infDist (prependPoint c (cubePoint b)) K^2/16))

theorem cubeProbability_nonneg {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ cubeProbability K := uniformProb_nonneg _

theorem cubeProbability_pos_nonempty {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (h : 0 < cubeProbability K) : K.Nonempty := by
  obtain ⟨b,hb⟩ := (uniformProb_pos_iff _).mp h
  exact ⟨cubePoint b,hb⟩

theorem cubeProbability_slices {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin (n+1)))) :
    cubeProbability K = (cubeProbability (coordinateSlice K 1)+
      cubeProbability (coordinateSlice K (-1)))/2 := by
  unfold cubeProbability
  rw [uniformProb_cons]
  simp [cubePoint_cons,bitSign,coordinateSlice]

theorem cubeDistanceMoment_slices {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin (n+1)))) :
    cubeDistanceMoment K = (sliceDistanceMoment K 1+sliceDistanceMoment K (-1))/2 := by
  unfold cubeDistanceMoment
  rw [uniformMean_cons]
  simp [cubePoint_cons,bitSign,sliceDistanceMoment]

theorem cubeDistanceMoment_zero {K : Set (EuclideanSpace ℝ (Fin 0))}
    (hp : 0 < cubeProbability K) : cubeDistanceMoment K ≤ 1/cubeProbability K := by
  obtain ⟨x,hx⟩ := cubeProbability_pos_nonempty hp
  have hall (b : Fin 0 → Bool) : cubePoint b ∈ K := by
    simpa only [Subsingleton.elim (cubePoint b) x] using hx
  have hpone : cubeProbability K = 1 := by simp [cubeProbability,uniformProb,hall]
  rw [hpone]
  have hmoment : cubeDistanceMoment K = 1 := by
    unfold cubeDistanceMoment
    simp only [Metric.infDist_zero_of_mem (hall _), zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Real.exp_zero, uniformMean_const]
  simp [hmoment]

end Stoc393

end
/- END original module: Stoc393.CubeProbability -/

/- BEGIN original module: Stoc393.Talagrand -/
section

/-! Talagrand's convex-set exponential-moment inequality on the uniform discrete cube. -/
open scoped BigOperators
open Set
set_option autoImplicit false
namespace Stoc393

theorem sliceDistanceMoment_bound {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hK : IsClosed K) (c d : ℝ) (hne : (coordinateSlice K d).Nonempty) :
    sliceDistanceMoment K c ≤ Real.exp ((c-d)^2/16)*cubeDistanceMoment (coordinateSlice K d) := by
  have hpoint (b : Fin n → Bool) := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (slice_infDist_bound hK c d hne (cubePoint b)) (by norm_num : (0 : ℝ) ≤ 16))
  have h := uniformMean_mono hpoint
  have heq (b : Fin n → Bool) : Real.exp (((c-d)^2+Metric.infDist (cubePoint b) (coordinateSlice K d)^2)/16) =
      Real.exp ((c-d)^2/16)*Real.exp (Metric.infDist (cubePoint b) (coordinateSlice K d)^2/16) := by
    rw [add_div,Real.exp_add]
  simp_rw [heq] at h
  rw [uniformMean_const_mul] at h
  exact h

theorem sliceDistanceMoment_same {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hK : IsClosed K) (c : ℝ) (hne : (coordinateSlice K c).Nonempty) :
    sliceDistanceMoment K c ≤ cubeDistanceMoment (coordinateSlice K c) := by
  simpa using sliceDistanceMoment_bound hK c c hne

theorem sliceDistanceMoment_mixing {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (c d : ℝ)
    (hne_c : (coordinateSlice K c).Nonempty) (hne_d : (coordinateSlice K d).Nonempty)
    {a b l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : cubeDistanceMoment (coordinateSlice K c) ≤ Real.exp a)
    (hd : cubeDistanceMoment (coordinateSlice K d) ≤ Real.exp b) :
    sliceDistanceMoment K c ≤ Real.exp (l^2*(c-d)^2/16+(1-l)*a+l*b) := by
  let f := fun bs : Fin n → Bool => Metric.infDist (cubePoint bs) (coordinateSlice K c)^2/16
  let g := fun bs : Fin n → Bool => Metric.infDist (cubePoint bs) (coordinateSlice K d)^2/16
  have hpoint (bs : Fin n → Bool) :
      Real.exp (Metric.infDist (prependPoint c (cubePoint bs)) K^2/16) ≤
        Real.exp (l^2*(c-d)^2/16)*Real.exp ((1-l)*f bs+l*g bs) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := slice_infDist_mixing hclosed hconvex c d hne_c hne_d (cubePoint bs) hl0 hl1
    dsimp [f,g]
    linarith
  have h := uniformMean_mono hpoint
  rw [uniformMean_const_mul] at h
  have hh := mul_le_mul_of_nonneg_left (uniformMean_exp_mixing f g hl0 hl1 hc hd)
    (Real.exp_nonneg (l^2*(c-d)^2/16))
  have hfinal := h.trans hh
  rw [← Real.exp_add] at hfinal
  convert hfinal using 1
  congr 1
  ring

/-- The dimension step after ordering the two slice probabilities. -/
theorem talagrand_ordered_step {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (c d : ℝ) (hcd : (c-d)^2 = 4)
    (hle : cubeProbability (coordinateSlice K c) ≤ cubeProbability (coordinateSlice K d))
    (hpd : 0 < cubeProbability (coordinateSlice K d))
    (ihc : 0 < cubeProbability (coordinateSlice K c) →
      cubeDistanceMoment (coordinateSlice K c) ≤ 1/cubeProbability (coordinateSlice K c))
    (ihd : cubeDistanceMoment (coordinateSlice K d) ≤ 1/cubeProbability (coordinateSlice K d)) :
    ((cubeProbability (coordinateSlice K c)+cubeProbability (coordinateSlice K d))/2)*
      ((sliceDistanceMoment K c+sliceDistanceMoment K d)/2) ≤ 1 := by
  let pc := cubeProbability (coordinateSlice K c)
  let pd := cubeProbability (coordinateSlice K d)
  have hpc : 0 ≤ pc := cubeProbability_nonneg _
  have hpd' : 0 < pd := hpd
  have hne_d := cubeProbability_pos_nonempty hpd
  have hMd : sliceDistanceMoment K d ≤ 1/pd := (sliceDistanceMoment_same hclosed d hne_d).trans ihd
  change ((pc+pd)/2)*((sliceDistanceMoment K c+sliceDistanceMoment K d)/2) ≤ 1
  by_cases hpcpos : 0 < pc
  · let r := pc/pd
    have hr0 : 0 ≤ r := div_nonneg hpc hpd.le
    have hr1 : r ≤ 1 := (div_le_one hpd).mpr hle
    obtain ⟨l,hl,hscalar⟩ := talagrand_scalar_average hr0 hr1
    have hepc : Real.exp (-Real.log pc) = 1/pc := by rw [Real.exp_neg, Real.exp_log hpcpos, one_div]
    have hepd : Real.exp (-Real.log pd) = 1/pd := by rw [Real.exp_neg, Real.exp_log hpd', one_div]
    have hMc := sliceDistanceMoment_mixing hclosed hconvex c d
      (cubeProbability_pos_nonempty hpcpos) hne_d hl.1 hl.2
      (hepc.symm ▸ ihc hpcpos) (hepd.symm ▸ ihd)
    rw [hcd] at hMc
    have hlog : Real.log r = Real.log pc-Real.log pd := Real.log_div hpcpos.ne' hpd.ne'
    have hexponent : l^2*4/16+(1-l)*(-Real.log pc)+l*(-Real.log pd) =
        (l^2/4-(1-l)*Real.log r)-Real.log pd := by rw [hlog]; ring
    rw [hexponent, Real.exp_sub, Real.exp_log hpd] at hMc
    have hsum := add_le_add hMc hMd
    have hscaled := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2))
      (show 0 ≤ (pc+pd)/2 by positivity)
    have hid : ((pc+pd)/2)*((Real.exp (l^2/4-(1-l)*Real.log r)/pd+1/pd)/2) =
        (1+r)/4*(1+Real.exp (l^2/4-(1-l)*Real.log r)) := by
      dsimp [r]
      field_simp [hpd'.ne']
      ring
    rw [hid] at hscaled
    exact hscaled.trans hscalar
  · have hpczero : pc = 0 := le_antisymm (le_of_not_gt hpcpos) hpc
    have hMc := (sliceDistanceMoment_bound hclosed c d hne_d).trans
      (mul_le_mul_of_nonneg_left ihd (Real.exp_nonneg _))
    rw [hcd] at hMc
    rw [show (4 : ℝ)/16 = 1/4 by norm_num] at hMc
    have hsum := add_le_add hMc hMd
    have hscaled := mul_le_mul_of_nonneg_left hsum hpd'.le
    have hid : pd*(Real.exp (1/4 : ℝ)*(1/pd)+1/pd) = Real.exp (1/4 : ℝ)+1 := by field_simp [hpd'.ne']
    rw [hid] at hscaled
    rw [hpczero]
    have he := exp_quarter_le_four_thirds
    nlinarith

/-- Lemma 2.1: exact exponential moment with the paper's constant 16. -/
theorem lemma_2_1 (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hp : 0 < cubeProbability K) :
    cubeDistanceMoment K ≤ 1/cubeProbability K := by
  induction n with
  | zero => exact cubeDistanceMoment_zero hp
  | succ n ih =>
    have ihp (c : ℝ) (hc : 0 < cubeProbability (coordinateSlice K c)) :
        cubeDistanceMoment (coordinateSlice K c) ≤ 1/cubeProbability (coordinateSlice K c) :=
      ih (coordinateSlice K c) (coordinateSlice_closed hclosed c) (coordinateSlice_convex hconvex c) hc
    apply (le_div_iff₀ hp).mpr
    rw [cubeProbability_slices, cubeDistanceMoment_slices]
    rw [mul_comm]
    have hprob := cubeProbability_slices K
    have hp0 := cubeProbability_nonneg (coordinateSlice K 1)
    have hm0 := cubeProbability_nonneg (coordinateSlice K (-1))
    by_cases hle : cubeProbability (coordinateSlice K 1) ≤ cubeProbability (coordinateSlice K (-1))
    · have hlarge : 0 < cubeProbability (coordinateSlice K (-1)) := by linarith
      exact talagrand_ordered_step hclosed hconvex 1 (-1) (by norm_num) hle hlarge (ihp 1) (ihp (-1) hlarge)
    · have hlarge : 0 < cubeProbability (coordinateSlice K 1) := by linarith
      have hstep := talagrand_ordered_step hclosed hconvex (-1) 1 (by norm_num)
        (le_of_not_ge hle) hlarge (ihp (-1)) (ihp 1 hlarge)
      simpa only [add_comm] using hstep

end Stoc393

end
/- END original module: Stoc393.Talagrand -/

/- BEGIN original module: Stoc393.BinomialBasics -/
section

/-! The exact binomial distribution of a uniform sum of signs. -/
open scoped BigOperators
open Finset
set_option autoImplicit false
namespace Stoc393

def positiveBits {k : ℕ} (b : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun j => b j = true)

def positiveBitsEquiv (k : ℕ) : (Fin k → Bool) ≃ Finset (Fin k) where
  toFun := positiveBits
  invFun s j := decide (j ∈ s)
  left_inv b := by
    funext j
    cases hj : b j <;> simp [positiveBits,hj]
  right_inv s := by ext j; simp [positiveBits]

theorem rademacherSum_eq_count {k : ℕ} (b : Fin k → Bool) :
    rademacherSum b = 2*((positiveBits b).card : ℝ)-k := by
  have hterm (j : Fin k) : bitSign (b j) = 2*(if b j = true then (1 : ℝ) else 0)-1 := by
    cases b j <;> norm_num [bitSign]
  unfold rademacherSum
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [positiveBits]

theorem mean_function_of_positive_count (k : ℕ) (g : ℕ → ℝ) :
    uniformMean (fun b : Fin k → Bool => g (positiveBits b).card) =
      (∑ r ∈ Finset.range (k+1), (k.choose r : ℝ)*g r)/(2:ℝ)^k := by
  have heq := uniformMean_equiv (positiveBitsEquiv k).symm
    (fun b : Fin k → Bool => g (positiveBits b).card)
  have hfun : (fun s : Finset (Fin k) => g (positiveBits ((positiveBitsEquiv k).symm s)).card) =
      fun s => g s.card := by
    funext s
    have h := (positiveBitsEquiv k).apply_symm_apply s
    change positiveBits ((positiveBitsEquiv k).symm s) = s at h
    rw [h]
  rw [hfun] at heq
  rw [← heq]
  unfold uniformMean
  have hsum := Finset.sum_powerset (Finset.univ : Finset (Fin k)) (fun s => g s.card)
  simp only [Finset.sum_powersetCard, nsmul_eq_mul, Finset.card_univ] at hsum
  simpa using congrArg (fun x : ℝ => x/(2:ℝ)^k) hsum

theorem rademacher_expectation_formula (k : ℕ) (g : ℝ → ℝ) :
    uniformMean (fun b : Fin k → Bool => g (rademacherSum b)) =
      (∑ r ∈ Finset.range (k+1), (k.choose r : ℝ)*g (2*(r : ℝ)-k))/(2:ℝ)^k := by
  simp_rw [rademacherSum_eq_count]
  exact mean_function_of_positive_count k (fun r => g (2*(r : ℝ)-k))

theorem positive_count_probability (k r : ℕ) :
    uniformProb (fun b : Fin k → Bool => (positiveBits b).card = r) = (k.choose r : ℝ)/(2:ℝ)^k := by
  classical
  rw [uniformProb_eq_indicator_mean, mean_function_of_positive_count k (fun j => if j = r then 1 else 0)]
  congr 1
  by_cases hr : r ≤ k
  · simp [hr]
  · have hchoose : k.choose r = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hr)
    simp [hr,hchoose]

end Stoc393

end
/- END original module: Stoc393.BinomialBasics -/

/- BEGIN original module: Stoc393.WallisBounds -/
section

/-! Exact central-binomial probability bounds from the Wallis integral estimates. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def centralProbability (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ)/(4:ℝ)^n

theorem centralProbability_pos (n : ℕ) : 0 < centralProbability n := by
  unfold centralProbability
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

theorem centralProbability_zero : centralProbability 0 = 1 := by simp [centralProbability]

theorem centralProbability_succ (n : ℕ) :
    centralProbability (n+1) = ((2*(n:ℝ)+1)/(2*n+2))*centralProbability n := by
  have hcast : ((n:ℝ)+1)*(Nat.centralBinom (n+1) : ℝ) =
      2*(2*n+1)*(Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hC : (Nat.centralBinom (n+1) : ℝ) = 2*(2*n+1)*(Nat.centralBinom n : ℝ)/(n+1) := by
    apply (eq_div_iff hn).mpr
    nlinarith
  unfold centralProbability
  rw [hC,pow_succ]
  field_simp
  ring

theorem centralProbability_wallis_identity (n : ℕ) :
    (2*(n:ℝ)+1)*centralProbability n^2*Real.Wallis.W n = 1 := by
  induction n with
  | zero => simp [centralProbability,Real.Wallis.W]
  | succ n ih =>
    calc
      (2*((n+1:ℕ):ℝ)+1)*centralProbability (n+1)^2*Real.Wallis.W (n+1) =
          (2*(n:ℝ)+1)*centralProbability n^2*Real.Wallis.W n := by
        rw [centralProbability_succ,Real.Wallis.W_succ]
        push_cast
        field_simp
        ring
      _ = 1 := ih

theorem centralProbability_sq_lower (n : ℕ) :
    2/(Real.pi*(2*(n:ℝ)+1)) ≤ centralProbability n^2 := by
  have hfactor : 0 ≤ (2*(n:ℝ)+1)*centralProbability n^2 := by positivity
  have h := mul_le_mul_of_nonneg_left (Real.Wallis.W_le n) hfactor
  rw [centralProbability_wallis_identity] at h
  apply (div_le_iff₀ (by positivity : 0 < Real.pi*(2*(n:ℝ)+1))).mpr
  nlinarith

theorem centralProbability_sq_upper {n : ℕ} (hn : 0 < n) :
    centralProbability n^2 ≤ 1/(Real.pi*(n:ℝ)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hfactor : 0 ≤ (2*(n:ℝ)+1)*centralProbability n^2 := by positivity
  have h := mul_le_mul_of_nonneg_left (Real.Wallis.le_W n) hfactor
  rw [centralProbability_wallis_identity] at h
  have hid : (2*(n:ℝ)+1)*centralProbability n^2*
      (((2:ℝ)*n+1)/(2*n+2)*(Real.pi/2)) =
      (Real.pi*(2*n+1)^2*centralProbability n^2)/(4*((n:ℝ)+1)) := by
    field_simp
    ring
  rw [hid] at h
  have hpoly := (div_le_one (by positivity : 0 < 4*((n:ℝ)+1))).mp h
  have hnonneg : 0 ≤ Real.pi*centralProbability n^2 := by positivity
  have hscaled : (centralProbability n^2*(Real.pi*n))*(4*((n:ℝ)+1)) ≤ 1*(4*((n:ℝ)+1)) := by
    nlinarith
  have hsmall := (mul_le_mul_iff_left₀ (by positivity : 0 < 4*((n:ℝ)+1))).mp hscaled
  exact (le_div_iff₀ (mul_pos Real.pi_pos hnR)).mpr hsmall

/-- Equation (16) in Appendix A, with the even sign count written as 2n. -/
theorem centralProbability_wallis_bounds {n : ℕ} (hn : 0 < n) :
    Real.sqrt (2/(Real.pi*(2*(n:ℝ)+1))) ≤ centralProbability n ∧
      centralProbability n ≤ Real.sqrt (2/(Real.pi*(2*(n:ℝ)))) := by
  have hl := Real.sqrt_le_sqrt (centralProbability_sq_lower n)
  have hu := Real.sqrt_le_sqrt (centralProbability_sq_upper hn)
  rw [Real.sqrt_sq (centralProbability_pos n).le] at hl hu
  refine ⟨hl,?_⟩
  convert hu using 1
  congr 1
  field_simp

end Stoc393

end
/- END original module: Stoc393.WallisBounds -/

/- BEGIN original module: Stoc393.RademacherAbsolute -/
section

/-! The exact absolute expectation of an even sum of signs and Lemma 2.2(a). -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem uniformMean_div_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    uniformMean (fun x => f x/c) = uniformMean f/c := by
  simp only [uniformMean, ← Finset.sum_div]
  ring

theorem integer_abs_step (z : ℤ) :
    (|(z:ℝ)+1|+|(z:ℝ)-1|)/2 = |(z:ℝ)|+(if (z:ℝ) = 0 then 1 else 0) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hzR : (z:ℝ) ≠ 0 := by exact_mod_cast hz
    rw [ite_eq_right hzR]
    by_cases hpos : 0 < z
    · have h1 : (1:ℝ) ≤ z := by exact_mod_cast (show (1:ℤ) ≤ z by omega)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z+1),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ z-1), abs_of_nonneg (by linarith : (0:ℝ) ≤ z)]
      ring
    · have h1 : (z:ℝ) ≤ -1 := by exact_mod_cast (show z ≤ (-1:ℤ) by omega)
      rw [abs_of_nonpos (by linarith : (z:ℝ)+1 ≤ 0),
        abs_of_nonpos (by linarith : (z:ℝ)-1 ≤ 0), abs_of_nonpos (by linarith : (z:ℝ) ≤ 0)]
      ring

theorem rademacherSum_cons {k : ℕ} (b : Bool) (bs : Fin k → Bool) :
    rademacherSum (Fin.cons b bs) = bitSign b+rademacherSum bs := by
  simp [rademacherSum,Fin.sum_univ_succ]

theorem rademacher_abs_step (k : ℕ) :
    uniformMean (fun b : Fin (k+1) → Bool => |rademacherSum b|) =
      uniformMean (fun b : Fin k → Bool => |rademacherSum b|)+
      uniformProb (fun b : Fin k → Bool => rademacherSum b = 0) := by
  classical
  have hpoint (b : Fin k → Bool) :
      (|1+rademacherSum b|+|-1+rademacherSum b|)/2 =
        |rademacherSum b|+(if rademacherSum b = 0 then 1 else 0) := by
    have hS : rademacherSum b = ((2*(positiveBits b).card:ℤ)-k : ℤ) := by
      rw [rademacherSum_eq_count]
      push_cast
      rfl
    rw [hS]
    simpa only [add_comm,sub_eq_add_neg] using integer_abs_step ((2*(positiveBits b).card:ℤ)-k)
  rw [uniformMean_cons]
  simp only [rademacherSum_cons,bitSign]
  norm_num only [Bool.false_eq_true,ite_false,ite_true]
  rw [← uniformMean_add, ← uniformMean_div_const]
  simp_rw [hpoint]
  rw [uniformMean_add, ← uniformProb_eq_indicator_mean]

theorem rademacher_zero_probability_even (n : ℕ) :
    uniformProb (fun b : Fin (2*n) → Bool => rademacherSum b = 0) = centralProbability n := by
  have heq : (fun b : Fin (2*n) → Bool => rademacherSum b = 0) =
      (fun b : Fin (2*n) → Bool => (positiveBits b).card = n) := by
    funext b
    apply propext
    rw [rademacherSum_eq_count]
    push_cast
    constructor
    · intro h
      have hh : ((positiveBits b).card:ℝ) = n := by linarith
      exact_mod_cast hh
    · intro h
      rw [h]
      ring
  rw [heq,positive_count_probability]
  unfold centralProbability Nat.centralBinom
  congr 1
  rw [pow_mul]
  norm_num

theorem rademacher_zero_probability_odd (n : ℕ) :
    uniformProb (fun b : Fin (2*n+1) → Bool => rademacherSum b = 0) = 0 := by
  have hnot (b : Fin (2*n+1) → Bool) : rademacherSum b ≠ 0 := by
    intro h
    rw [rademacherSum_eq_count] at h
    push_cast at h
    have hcast : (2:ℝ)*(positiveBits b).card = 2*(n:ℝ)+1 := by linarith
    have hnat : 2*(positiveBits b).card = 2*n+1 := by exact_mod_cast hcast
    omega
  simp [uniformProb,hnot]

theorem rademacher_abs_expectation_even (n : ℕ) :
    uniformMean (fun b : Fin (2*n) → Bool => |rademacherSum b|) = 2*(n:ℝ)*centralProbability n := by
  induction n with
  | zero => simp [uniformMean,rademacherSum]
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, rademacher_abs_step,
      rademacher_zero_probability_odd, add_zero, rademacher_abs_step,
      rademacher_zero_probability_even, ih, centralProbability_succ]
    push_cast
    field_simp

theorem centralProbability_decimal_bound {n : ℕ} (hn : 0 < n) :
    (n:ℝ)*centralProbability n^2 ≤ 8/25 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbound := (le_div_iff₀ (mul_pos Real.pi_pos hnR)).mp (centralProbability_sq_upper hn)
  have hfirst : (n:ℝ)*centralProbability n^2 ≤ 1/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith
  have hsecond : (1:ℝ)/Real.pi ≤ 8/25 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_d2]
  exact hfirst.trans hsecond

/-- Lemma 2.2(a), for every even k >= 2. -/
theorem lemma_2_2_a {k : ℕ} (hk : 2 ≤ k) (heven : Even k) :
    uniformMean (fun b : Fin k → Bool => |rademacherSum b|) ≤ (4/5)*Real.sqrt k := by
  obtain ⟨n,hn⟩ := heven
  have heq : k = 2*n := by omega
  clear hn
  subst k
  have hnpos : 0 < n := by omega
  rw [rademacher_abs_expectation_even]
  have hbound := mul_le_mul_of_nonneg_left (centralProbability_decimal_bound hnpos)
    (show 0 ≤ 4*(n:ℝ) by positivity)
  have hsqrt := Real.sq_sqrt (show 0 ≤ ((2*n:ℕ):ℝ) by positivity)
  have hp := Real.sqrt_nonneg ((2*n:ℕ):ℝ)
  have hnonneg : 0 ≤ 2*(n:ℝ)*centralProbability n := by
    have h := (centralProbability_pos n).le
    positivity
  apply (sq_le_sq₀ hnonneg (show 0 ≤ (4/5)*Real.sqrt ((2*n:ℕ):ℝ) by positivity)).mp
  push_cast at hsqrt ⊢
  nlinarith

end Stoc393

end
/- END original module: Stoc393.RademacherAbsolute -/

/- BEGIN original module: Stoc393.BinomialCDF -/
section

/-! Binomial cumulative sums and their monotone adjacent ratios. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def binomialPrefix (k j : ℕ) : ℝ := ∑ i ∈ Finset.range (j+1), (k.choose i : ℝ)
noncomputable def binomialCDF (k j : ℕ) : ℝ := binomialPrefix k j/(2:ℝ)^k

theorem binomialPrefix_succ (k j : ℕ) :
    binomialPrefix k (j+1) = binomialPrefix k j+(k.choose (j+1):ℝ) := by
  exact Finset.sum_range_succ _ _

theorem binomialPrefix_pos (k j : ℕ) : 0 < binomialPrefix k j := by
  have h : (1:ℝ) ≤ binomialPrefix k j := by
    simpa only [binomialPrefix, Nat.choose_zero_right,Nat.cast_one] using
      (Finset.single_le_sum (s := Finset.range (j+1)) (f := fun i => (k.choose i:ℝ))
        (fun i _ => Nat.cast_nonneg _) (show 0 ∈ Finset.range (j+1) by simp))
  linarith

theorem choose_succ_ratio {k j : ℕ} (hj : j ≤ k) :
    (k.choose (j+1):ℝ) = (k.choose j:ℝ)*((k:ℝ)-j)/((j:ℝ)+1) := by
  have h := Nat.choose_succ_right_eq k j
  have hc : (k.choose (j+1):ℝ)*((j:ℝ)+1) = (k.choose j:ℝ)*((k:ℝ)-j) := by
    exact_mod_cast h
  exact (eq_div_iff (by positivity)).mpr hc

theorem choose_adjacent_cross {k i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (k.choose i:ℝ)*(k.choose (j+1):ℝ) ≤ (k.choose (i+1):ℝ)*(k.choose j:ℝ) := by
  have hiR : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hkR : (j:ℝ) ≤ k := by exact_mod_cast hjk
  have hratio : ((k:ℝ)-j)/((j:ℝ)+1) ≤ ((k:ℝ)-i)/((i:ℝ)+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) (sub_nonneg.mpr hiR)
    nlinarith
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (k.choose i:ℝ)*(k.choose j:ℝ) by positivity)
  rw [choose_succ_ratio hjk, choose_succ_ratio (hij.trans hjk)]
  convert h using 1 <;> ring

theorem binomialPrefix_hazard {k j : ℕ} (hj : j+1 ≤ k) :
    binomialPrefix k j*(k.choose (j+2):ℝ) ≤ binomialPrefix k (j+1)*(k.choose (j+1):ℝ) := by
  have hsum := Finset.sum_le_sum (s := Finset.range (j+1))
    (fun i hi => choose_adjacent_cross (show i ≤ j+1 by have h := Finset.mem_range.mp hi; omega) hj)
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have htail : (∑ i ∈ Finset.range (j+1), (k.choose (i+1):ℝ)) ≤ binomialPrefix k (j+1) := by
    have h := Finset.sum_range_succ' (fun i => (k.choose i:ℝ)) (j+1)
    unfold binomialPrefix
    rw [h]
    simp
  exact hsum.trans (mul_le_mul_of_nonneg_right htail (Nat.cast_nonneg _))

theorem binomialPrefix_ratio_step {k j : ℕ} (hj : j+1 ≤ k) :
    binomialPrefix k j/binomialPrefix k (j+1) ≤
      binomialPrefix k (j+1)/binomialPrefix k (j+2) := by
  apply (div_le_div_iff₀ (binomialPrefix_pos k (j+1)) (binomialPrefix_pos k (j+2))).mpr
  have h := binomialPrefix_hazard hj
  rw [show j+2 = (j+1)+1 by omega, binomialPrefix_succ] at h ⊢
  have hrec := binomialPrefix_succ k j
  rw [hrec]
  nlinarith

theorem binomialPrefix_ratio_mono {k i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    binomialPrefix k i/binomialPrefix k (i+1) ≤ binomialPrefix k j/binomialPrefix k (j+1) := by
  induction hij with
  | refl => rfl
  | @step j hij ih =>
    exact (ih (by omega)).trans (binomialPrefix_ratio_step (by omega))

theorem positive_count_cdf_probability {k j : ℕ} (hj : j ≤ k) :
    uniformProb (fun b : Fin k → Bool => (positiveBits b).card ≤ j) = binomialCDF k j := by
  classical
  rw [uniformProb_eq_indicator_mean, mean_function_of_positive_count k (fun i => if i ≤ j then 1 else 0)]
  unfold binomialCDF binomialPrefix
  congr 1
  have hfilter : (Finset.range (k+1)).filter (fun i => i ≤ j) = Finset.range (j+1) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter]

end Stoc393

end
/- END original module: Stoc393.BinomialCDF -/

/- BEGIN original module: Stoc393.BinomialCenter -/
section

/-! Binomial masses, the two central cumulative probabilities, and the last lower-tail ratio. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def binomialMass (k j : ℕ) : ℝ := (k.choose j:ℝ)/(2:ℝ)^k

theorem binomialMass_nonneg (k j : ℕ) : 0 ≤ binomialMass k j := by
  unfold binomialMass
  positivity

theorem binomialCDF_pos (k j : ℕ) : 0 < binomialCDF k j :=
  div_pos (binomialPrefix_pos k j) (by positivity)

theorem binomialCDF_succ (k j : ℕ) :
    binomialCDF k (j+1) = binomialCDF k j+binomialMass k (j+1) := by
  simp only [binomialCDF, binomialPrefix_succ, add_div, binomialMass]

theorem binomialMass_center (n : ℕ) : binomialMass (2*n) n = centralProbability n := by
  unfold binomialMass centralProbability Nat.centralBinom
  rw [pow_mul]
  norm_num

theorem binomialMass_le_center (n j : ℕ) : binomialMass (2*n) j ≤ centralProbability n := by
  rw [← binomialMass_center n]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_centralBinom j n

theorem rademacher_negative_probability (n : ℕ) :
    uniformProb (fun b : Fin (2*n) → Bool => rademacherSum b < 0) = (1-centralProbability n)/2 := by
  classical
  have hsym := uniformProb_equiv (negateBits (2*n)) (fun b => rademacherSum b < 0)
  simp only [rademacherSum_negate, neg_lt_zero] at hsym
  have hpoint (b : Fin (2*n) → Bool) :
      (if rademacherSum b < 0 then (1:ℝ) else 0)+
      (if rademacherSum b = 0 then 1 else 0)+
      (if 0 < rademacherSum b then 1 else 0) = 1 := by
    rcases lt_trichotomy (rademacherSum b) 0 with h|h|h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
  have htotal := congrArg (fun f : (Fin (2*n) → Bool) → ℝ => uniformMean f) (funext hpoint)
  rw [uniformMean_add, uniformMean_add, uniformMean_const,
    ← uniformProb_eq_indicator_mean, ← uniformProb_eq_indicator_mean,
    ← uniformProb_eq_indicator_mean, hsym, rademacher_zero_probability_even] at htotal
  linarith

theorem binomialCDF_below_center {n : ℕ} (hn : 0 < n) :
    binomialCDF (2*n) (n-1) = (1-centralProbability n)/2 := by
  rw [← positive_count_cdf_probability (by omega : n-1 ≤ 2*n),
    ← rademacher_negative_probability n]
  congr 1
  funext b
  apply propext
  rw [rademacherSum_eq_count]
  push_cast
  constructor
  · intro h
    have hcast : ((positiveBits b).card:ℝ) < n := by exact_mod_cast (show (positiveBits b).card < n by omega)
    linarith
  · intro h
    have hcast : ((positiveBits b).card:ℝ) < n := by linarith
    have hnat : (positiveBits b).card < n := by exact_mod_cast hcast
    omega

theorem binomialCDF_center {n : ℕ} (hn : 0 < n) :
    binomialCDF (2*n) n = (1+centralProbability n)/2 := by
  have h := binomialCDF_succ (2*n) (n-1)
  rw [Nat.sub_add_cancel hn, binomialCDF_below_center hn, binomialMass_center] at h
  linarith

theorem centralProbability_lt_one {n : ℕ} (hn : 0 < n) : centralProbability n < 1 := by
  have h := binomialCDF_pos (2*n) (n-1)
  rw [binomialCDF_below_center hn] at h
  linarith

theorem binomialMass_before_center {n : ℕ} (hn : 0 < n) :
    binomialMass (2*n) (n-1) = (n:ℝ)/(n+1)*centralProbability n := by
  have h := choose_succ_ratio (show n-1 ≤ 2*n by omega)
  rw [Nat.sub_add_cancel hn] at h
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hncast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub hn]; norm_num
  rw [hncast] at h
  push_cast at h
  have hprod := (eq_div_iff (by linarith : (n:ℝ)-1+1 ≠ 0)).mp h
  rw [← binomialMass_center n]
  unfold binomialMass
  field_simp
  nlinarith

theorem binomialCDF_last_lower_ratio {n : ℕ} (hn : 2 ≤ n) :
    binomialCDF (2*n) (n-2)/binomialCDF (2*n) (n-1) =
      1-(2*(n:ℝ)*centralProbability n)/((n+1)*(1-centralProbability n)) := by
  have hs := binomialCDF_succ (2*n) (n-2)
  rw [show n-2+1 = n-1 by omega, binomialCDF_below_center (by omega),
    binomialMass_before_center (by omega)] at hs
  have hden : 1-centralProbability n ≠ 0 := by
    have h := centralProbability_lt_one (by omega : 0 < n)
    linarith
  have hnR : (n:ℝ)+1 ≠ 0 := by positivity
  rw [binomialCDF_below_center (by omega)]
  have hval : binomialCDF (2*n) (n-2) =
      (1-centralProbability n)/2-(n:ℝ)/(n+1)*centralProbability n := by linarith
  rw [hval]
  field_simp

theorem binomialCDF_ratio_mono {k i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    binomialCDF k i/binomialCDF k (i+1) ≤ binomialCDF k j/binomialCDF k (j+1) := by
  have hp : (2:ℝ)^k ≠ 0 := by positivity
  simpa only [binomialCDF, div_div_div_cancel_right₀ hp] using binomialPrefix_ratio_mono hij hj

end Stoc393

end
/- END original module: Stoc393.BinomialCenter -/

/- BEGIN original module: Stoc393.BinomialTailScalar -/
section

/-! Scalar estimates for the sharp binomial lower tail. -/
open Set
set_option autoImplicit false
namespace Stoc393

theorem one_sub_div_one_add_le_exp {x : ℝ} (hx : 0 ≤ x) :
    (1-x)/(1+x) ≤ Real.exp (-2*x) := by
  let f : ℝ → ℝ := fun y => (1-y)*Real.exp (2*y)-(1+y)
  have hd (y : ℝ) : HasDerivAt f ((1-2*y)*Real.exp (2*y)-1) y := by
    convert ((((hasDerivAt_id y).const_sub 1).mul
      (((hasDerivAt_id y).const_mul 2).exp)).sub
      ((hasDerivAt_id y).const_add 1)) using 1
    · ext z
      dsimp [f]
    · dsimp
      ring
  have hmono : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · intro y hy
      exact (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2*y))
        (Real.exp_nonneg (2*y))
      have hid : Real.exp (-2*y)*Real.exp (2*y) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      rw [hid] at h
      nlinarith
  have h := hmono (show (0:ℝ) ∈ Ici 0 by simp) hx hx
  have hf : (1-x)*Real.exp (2*x) ≤ 1+x := by
    simpa [f] using h
  have hmul := mul_le_mul_of_nonneg_right hf (Real.exp_nonneg (-2*x))
  have hid : Real.exp (2*x)*Real.exp (-2*x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [mul_assoc, hid, mul_one] at hmul
  exact (div_le_iff₀ (by linarith : 0 < 1+x)).mpr (by nlinarith)

theorem binomial_rate_auxiliary {k : ℝ} (hk : 2 ≤ k) :
    let a := Real.sqrt (2/(Real.pi*k))
    let r := Real.sqrt (1+1/k)
    r ≤ 1+a/2 ∧ (k+2)*r ≤ k+2*(k+1)*a := by
  dsimp
  have hkpos : 0 < k := by linarith
  have hkne := ne_of_gt hkpos
  have hpi := ne_of_gt Real.pi_pos
  have ha := Real.sqrt_nonneg (2/(Real.pi*k))
  have hasq := Real.sq_sqrt (show 0 ≤ 2/(Real.pi*k) by positivity)
  have haid : Real.sqrt (2/(Real.pi*k))^2*k = 2/Real.pi := by
    rw [hasq]
    field_simp
  have hsmall : 1/k ≤ Real.sqrt (2/(Real.pi*k)) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (mul_pos Real.pi_pos hkpos)).mpr
    field_simp
    nlinarith [Real.pi_lt_four]
  have hr := Real.sqrt_one_add_le (show -1 ≤ 1/k by
    linarith [show (0:ℝ) ≤ 1/k by positivity])
  have hhalf : 1/k ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hkpos).mpr
    linarith
  have hpibound : (9:ℝ)/16 ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d2]
  have hbig : 3 ≤ 2*(k+1)*Real.sqrt (2/(Real.pi*k)) := by
    have hquad := mul_nonneg (sq_nonneg (k-1))
      (sq_nonneg (Real.sqrt (2/(Real.pi*k))))
    have hsign : 0 ≤ 2*(k+1)*Real.sqrt (2/(Real.pi*k)) := by positivity
    nlinarith
  refine ⟨by linarith,?_⟩
  have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ k+2 by linarith)
  have hid : (k+2)*(1+(1/k)/2) = k+5/2+1/k := by
    field_simp
    ring
  rw [hid] at h
  linarith

theorem binomial_lower_start_scalar {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbr : a ≤ b*r) (hr : r ≤ 1+a/2) :
    (1-b)/2 ≤ (1/2)*Real.exp (-a) := by
  have hprod := (mul_le_mul_of_nonneg_left hr hb)
  have hrat : 1-b ≤ (1-a/2)/(1+a/2) := by
    apply (le_div_iff₀ (by linarith : 0 < 1+a/2)).mpr
    nlinarith
  have hexp := one_sub_div_one_add_le_exp (show 0 ≤ a/2 by positivity)
  have heq : -2*(a/2) = -a := by ring
  rw [heq] at hexp
  linarith

theorem binomial_lower_ratio_scalar {k a b r : ℝ}
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b < 1)
    (hbr : a ≤ b*r) (hr : (k+2)*r ≤ k+2*(k+1)*a) :
    1-(2*k*b)/((k+2)*(1-b)) ≤ Real.exp (-2*a) := by
  have hprod := mul_le_mul_of_nonneg_left hr hb
  have hprod' := mul_le_mul_of_nonneg_left hbr (show 0 ≤ k+2 by linarith)
  have hmain : a*(k+2)*(1-b) ≤ k*b*(1+a) := by nlinarith
  have hratio : (2*a)/(1+a) ≤ (2*k*b)/((k+2)*(1-b)) := by
    apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
    nlinarith
  have hid : 1-(2*a)/(1+a) = (1-a)/(1+a) := by field_simp; ring
  have hexp := one_sub_div_one_add_le_exp ha
  rw [← hid] at hexp
  linarith

end Stoc393

end
/- END original module: Stoc393.BinomialTailScalar -/

/- BEGIN original module: Stoc393.BinomialTail -/
section

/-! The exponential cumulative-binomial bound, Equation (17) in Appendix A. -/
set_option autoImplicit false
namespace Stoc393

noncomputable def binomialRate (n : ℕ) : ℝ := Real.sqrt (2/(Real.pi*(2*(n:ℝ))))

theorem binomialRate_nonneg (n : ℕ) : 0 ≤ binomialRate n := Real.sqrt_nonneg _

theorem centralProbability_rate_lower {n : ℕ} (hn : 0 < n) :
    binomialRate n ≤ centralProbability n*Real.sqrt (1+1/(2*(n:ℝ))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_right (centralProbability_wallis_bounds hn).1
    (Real.sqrt_nonneg (1+1/(2*(n:ℝ))))
  have hid : Real.sqrt (2/(Real.pi*(2*(n:ℝ)+1)))*Real.sqrt (1+1/(2*(n:ℝ))) =
      binomialRate n := by
    rw [← Real.sqrt_mul (show 0 ≤ 2/(Real.pi*(2*(n:ℝ)+1)) by positivity)]
    unfold binomialRate
    congr 1
    field_simp
  rwa [hid] at h

theorem binomialCDF_start_exp {n : ℕ} (hn : 0 < n) :
    binomialCDF (2*n) (n-1) ≤ (1/2)*Real.exp (-binomialRate n) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr := (binomial_rate_auxiliary (show (2:ℝ) ≤ 2*(n:ℝ) by linarith)).1
  rw [binomialCDF_below_center hn]
  exact binomial_lower_start_scalar (binomialRate_nonneg n) (centralProbability_pos n).le
    (centralProbability_rate_lower hn) hr

theorem binomialCDF_step_exp {n j : ℕ} (hj : j+1 < n) :
    binomialCDF (2*n) j ≤ Real.exp (-2*binomialRate n)*binomialCDF (2*n) (j+1) := by
  have hn : 2 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hmono := binomialCDF_ratio_mono (show j ≤ n-2 by omega) (show n-2 ≤ 2*n by omega)
  rw [show n-2+1 = n-1 by omega, binomialCDF_last_lower_ratio hn] at hmono
  have hr := (binomial_rate_auxiliary (show (2:ℝ) ≤ 2*(n:ℝ) by linarith)).2
  have hscalar := binomial_lower_ratio_scalar (show 0 ≤ 2*(n:ℝ) by positivity)
    (binomialRate_nonneg n) (centralProbability_pos n).le (centralProbability_lt_one (by omega))
    (centralProbability_rate_lower (by omega : 0 < n)) hr
  have hid : (2*(2*(n:ℝ))*centralProbability n)/((2*n+2)*(1-centralProbability n)) =
      (2*(n:ℝ)*centralProbability n)/((n+1)*(1-centralProbability n)) := by
    field_simp
  rw [hid] at hscalar
  exact (div_le_iff₀ (binomialCDF_pos (2*n) (j+1))).mp (hmono.trans hscalar)

theorem binomialCDF_lower_exp {n : ℕ} (hn : 0 < n) (r : ℕ) (hr : r < n) :
    binomialCDF (2*n) (n-1-r) ≤ (1/2)*Real.exp (-binomialRate n*(2*(r:ℝ)+1)) := by
  induction r with
  | zero => simpa using binomialCDF_start_exp hn
  | succ r ih =>
    have hprev := ih (by omega)
    have hstep := binomialCDF_step_exp (show (n-1-(r+1))+1 < n by omega)
    rw [show n-1-(r+1)+1 = n-1-r by omega] at hstep
    have h := hstep.trans (mul_le_mul_of_nonneg_left hprev (Real.exp_nonneg _))
    convert h using 1
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    push_cast
    ring

theorem binomialCDF_upper_linear {n j : ℕ} (hn : 0 < n) (hj : n ≤ j) :
    binomialCDF (2*n) j ≤ (1+centralProbability n*(2*(j:ℝ)-2*n+1))/2 := by
  induction hj with
  | refl => simpa using (binomialCDF_center hn).le
  | @step j hj ih =>
    rw [binomialCDF_succ]
    have h := binomialMass_le_center n (j+1)
    push_cast
    nlinarith

theorem binomialCDF_exp_bound {n : ℕ} (hn : 0 < n) (j : ℕ) :
    binomialCDF (2*n) j ≤ (1/2)*Real.exp (binomialRate n*(2*(j:ℝ)-2*n+1)) := by
  by_cases hj : n ≤ j
  · have h := binomialCDF_upper_linear hn hj
    have hβ := (centralProbability_wallis_bounds hn).2
    have hfactor : 0 ≤ 2*(j:ℝ)-2*n+1 := by
      have hc : (n:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hmul := mul_le_mul_of_nonneg_right hβ hfactor
    have he := Real.add_one_le_exp (binomialRate n*(2*(j:ℝ)-2*n+1))
    change centralProbability n*(2*(j:ℝ)-2*n+1) ≤ binomialRate n*(2*(j:ℝ)-2*n+1) at hmul
    linarith
  · have h := binomialCDF_lower_exp hn (n-1-j) (by omega)
    rw [show n-1-(n-1-j) = j by omega] at h
    have hc : ((n-1-j:ℕ):ℝ) = (n:ℝ)-1-j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hn]
      norm_num
    rw [hc] at h
    convert h using 1
    congr 2
    ring

end Stoc393

end
/- END original module: Stoc393.BinomialTail -/

/- BEGIN original module: Stoc393.RademacherTail -/
section

/-! Lemma 2.2(c), including arbitrary real thresholds. -/
set_option autoImplicit false
namespace Stoc393

theorem binomialRate_mul_sqrt {n : ℕ} (hn : 0 < n) :
    binomialRate n*Real.sqrt ((2*n:ℕ):ℝ) = Real.sqrt (2/Real.pi) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  unfold binomialRate
  rw [← Real.sqrt_mul (show 0 ≤ 2/(Real.pi*(2*(n:ℝ))) by positivity)]
  congr 1
  push_cast
  field_simp

theorem lemma_2_2_c {k : ℕ} (hk : 2 ≤ k) (heven : Even k) (t : ℝ) :
    uniformProb (fun b : Fin k → Bool => rademacherSum b ≤ t*Real.sqrt k-1) ≤
      (1/2)*Real.exp (Real.sqrt (2/Real.pi)*t) := by
  classical
  obtain ⟨n,hn⟩ := heven
  have heq : k = 2*n := by omega
  clear hn
  subst k
  have hn : 0 < n := by omega
  let T : ℝ := t*Real.sqrt ((2*n:ℕ):ℝ)-1
  by_cases hT : T < -(2*(n:ℝ))
  · have hempty (b : Fin (2*n) → Bool) : ¬ rademacherSum b ≤ T := by
      rw [rademacherSum_eq_count]
      push_cast
      have hc : (0:ℝ) ≤ (positiveBits b).card := by positivity
      linarith
    change uniformProb (fun b : Fin (2*n) → Bool => rademacherSum b ≤ T) ≤ _
    simp only [uniformProb, hempty, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity
  · have hX : 0 ≤ (T+2*(n:ℝ))/2 := by linarith
    let j := min (2*n) (Nat.floor ((T+2*(n:ℝ))/2))
    have hj : j ≤ 2*n := Nat.min_le_left _ _
    have hevent : (fun b : Fin (2*n) → Bool => rademacherSum b ≤ T) =
        (fun b : Fin (2*n) → Bool => (positiveBits b).card ≤ j) := by
      funext b
      apply propext
      have hc : (positiveBits b).card ≤ 2*n := by
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin (2*n))
      simp only [j, le_min_iff, hc, true_and, Nat.le_floor_iff hX, rademacherSum_eq_count]
      push_cast
      constructor <;> intro h <;> linarith
    change uniformProb (fun b : Fin (2*n) → Bool => rademacherSum b ≤ T) ≤ _
    rw [hevent, positive_count_cdf_probability hj]
    have hbound := binomialCDF_exp_bound hn j
    have hjfloor : j ≤ Nat.floor ((T+2*(n:ℝ))/2) := Nat.min_le_right _ _
    have hjR := (Nat.le_floor_iff hX).mp hjfloor
    have hterm : 2*(j:ℝ)-2*n+1 ≤ t*Real.sqrt ((2*n:ℕ):ℝ) := by
      dsimp [T] at hjR
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hterm (binomialRate_nonneg n)
    have hid : binomialRate n*(t*Real.sqrt ((2*n:ℕ):ℝ)) = Real.sqrt (2/Real.pi)*t := by
      rw [mul_left_comm, binomialRate_mul_sqrt hn, mul_comm]
    rw [hid] at hscaled
    exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscaled) (by norm_num))

end Stoc393

end
/- END original module: Stoc393.RademacherTail -/

/- BEGIN original module: Stoc393.PerturbedTailScalar -/
section

/-! Exact constants for the three ranges in Lemma 2.2(d). -/
set_option autoImplicit false
namespace Stoc393

noncomputable def signTailConstant : ℝ := Real.sqrt (2/Real.pi)

theorem signTailConstant_bounds : (3:ℝ)/4 ≤ signTailConstant ∧ signTailConstant ≤ 4/5 := by
  unfold signTailConstant
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d2]
  · apply (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 4/5)).mpr
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_d2]

theorem signTailConstant_identity : signTailConstant/2 = 1/Real.sqrt (2*Real.pi) := by
  have hp : (0:ℝ) < 2*Real.pi := by positivity
  have hsq := Real.sq_sqrt hp.le
  have hC := Real.sq_sqrt (show 0 ≤ 2/Real.pi by positivity)
  have hn := Real.sqrt_nonneg (2/Real.pi)
  have hn' := Real.sqrt_nonneg (2*Real.pi)
  have hmul : Real.sqrt (2/Real.pi)*Real.sqrt (2*Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    have hid : (2/Real.pi)*(2*Real.pi) = (4:ℝ) := by field_simp; norm_num
    rw [hid]
    norm_num
  unfold signTailConstant
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hp))).mpr
  nlinarith

theorem delta_value : delta = (1:ℝ)/4194304 := by norm_num [delta]

theorem sqrt_delta_value : Real.sqrt delta = (1:ℝ)/2048 := by
  rw [delta_value]
  norm_num

theorem perturbed_exponent_identity (u : ℝ) :
    4*Real.sqrt delta+(1-u^2)/Real.sqrt (2*Real.pi*delta) =
      1/512+1024*signTailConstant*(1-u^2) := by
  rw [sqrt_delta_value, Real.sqrt_mul (show 0 ≤ 2*Real.pi by positivity), sqrt_delta_value]
  have hid := signTailConstant_identity
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp at hid ⊢
  nlinarith

theorem perturbed_low_exponent {u : ℝ} (hu : 0 ≤ u) (hsmall : u ≤ 1-(5/2)*(1/2048:ℝ)) :
    1 ≤ 1/512+1024*signTailConstant*(1-u^2) := by
  have hsq : u^2 ≤ (1-(5/2)*(1/2048:ℝ))^2 := by
    nlinarith [sq_nonneg (u-(1-(5/2)*(1/2048:ℝ)))]
  have hpos : 0 ≤ 1-u^2 := by nlinarith
  have hC := mul_le_mul_of_nonneg_right signTailConstant_bounds.1 hpos
  nlinarith

theorem perturbed_middle_exponent {u q : ℝ}
    (hu : |u-1| ≤ (5/2)*(1/2048:ℝ)) (hq : q ≤ (1:ℝ)/4096) :
    signTailConstant*((1+(1:ℝ)/4194304-u)*2048+q) ≤
      1/512+1024*signTailConstant*(1-u^2) := by
  have hsq : (u-1)^2 ≤ ((5/2)*(1/2048:ℝ))^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hu
  have hC := signTailConstant_bounds
  have hdiff : 1024*(u-1)^2+(1:ℝ)/2048+q ≤ (37:ℝ)/16384 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ signTailConstant by linarith [hC.1])
  have hupper := mul_le_mul_of_nonneg_right hC.2 (show 0 ≤ (37:ℝ)/16384 by norm_num)
  nlinarith

theorem perturbed_high_exponent {h : ℝ} (hh : (5:ℝ)/2 ≤ h) :
    -(h-(1:ℝ)/2048)^2/2+1 ≤
      1024*signTailConstant*(1-(1+h/2048)^2) := by
  have hC := signTailConstant_bounds
  have hpos : 0 ≤ h+h^2/4096 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC.2 hpos
  have hquad := mul_nonneg (show 0 ≤ h-(5:ℝ)/2 by linarith)
    (show 0 ≤ h+(5:ℝ)/2 by linarith)
  nlinarith [sq_nonneg (h-(5:ℝ)/2)]

end Stoc393

end
/- END original module: Stoc393.PerturbedTailScalar -/

/- BEGIN original module: Stoc393.PerturbedTail -/
section

/-! The three-range probability argument for Lemma 2.2(d). -/
set_option autoImplicit false
namespace Stoc393

theorem exp_le_half_exp_of_add_one_le {x y : ℝ} (h : x+1 ≤ y) :
    Real.exp x ≤ (1/2)*Real.exp y := by
  have hmon := Real.exp_le_exp.mpr h
  rw [Real.exp_add] at hmon
  have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1:ℝ)) (Real.exp_nonneg x)
  nlinarith

theorem perturbed_tail_normalized {k : ℕ} (hk : 2^24 ≤ k) (heven : Even k)
    {u : ℝ} (hu : 0 ≤ u) :
    uniformProb (fun b : Fin k → Bool =>
      u+(1/2048)*(rademacherSum b/Real.sqrt k) ≤ 1+(1:ℝ)/4194304) ≤
      (1/2)*Real.exp (1/512+1024*signTailConstant*(1-u^2)) := by
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hspos : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hkpos)
  have hsne := ne_of_gt hspos
  have hK : (4096:ℝ) ≤ Real.sqrt k := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hk
  have hq : 1/Real.sqrt (k:ℝ) ≤ (1:ℝ)/4096 := by
    apply (div_le_iff₀ hspos).mpr
    linarith
  by_cases hlo : u ≤ 1-(5/2)*(1/2048:ℝ)
  · have hE := perturbed_low_exponent hu hlo
    have he := Real.add_one_le_exp (1/512+1024*signTailConstant*(1-u^2))
    have hprob := uniformProb_le_one (fun b : Fin k → Bool =>
      u+(1/2048)*(rademacherSum b/Real.sqrt k) ≤ 1+(1:ℝ)/4194304)
    linarith
  · by_cases hhi : u ≤ 1+(5/2)*(1/2048:ℝ)
    · have hmid : |u-1| ≤ (5/2)*(1/2048:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
      let t : ℝ := (1+(1:ℝ)/4194304-u)*2048+1/Real.sqrt k
      have hp := uniformProb_mono (Q := fun b : Fin k → Bool => rademacherSum b ≤ t*Real.sqrt k-1)
        (fun b (hb : u+(1/2048)*(rademacherSum b/Real.sqrt k) ≤ 1+(1:ℝ)/4194304) => by
          have hr : rademacherSum b/Real.sqrt k ≤ (1+(1:ℝ)/4194304-u)*2048 := by linarith
          have hmul := (div_le_iff₀ hspos).mp hr
          have hinv : (1/Real.sqrt (k:ℝ))*Real.sqrt k = 1 := by field_simp
          dsimp [t]
          nlinarith)
      have hc := lemma_2_2_c hk2 heven t
      have hE := perturbed_middle_exponent hmid hq
      change signTailConstant*t ≤ 1/512+1024*signTailConstant*(1-u^2) at hE
      exact (hp.trans hc).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (by norm_num))
    · let h : ℝ := (u-1)*2048
      have hh : (5:ℝ)/2 ≤ h := by dsimp [h]; linarith
      have ha : 0 ≤ h-(1:ℝ)/2048 := by linarith
      have hp := uniformProb_mono
        (Q := fun b : Fin k → Bool => rademacherSum b/Real.sqrt k ≤ -(h-(1:ℝ)/2048))
        (fun b (hb : u+(1/2048)*(rademacherSum b/Real.sqrt k) ≤ 1+(1:ℝ)/4194304) => by
          dsimp [h]
          linarith)
      have hc := rademacher_normalized_lower_tail hkpos ha
      have hE := perturbed_high_exponent hh
      have huEq : 1+h/2048 = u := by dsimp [h]; ring
      rw [huEq] at hE
      have hE' : -(h-(1:ℝ)/2048)^2/2+1 ≤ 1/512+1024*signTailConstant*(1-u^2) := by linarith
      exact (hp.trans hc).trans (exp_le_half_exp_of_add_one_le hE')

/-- Lemma 2.2(d), for the paper's fixed delta = 2^(-22). -/
theorem lemma_2_2_d {k : ℕ} (hk : 2^24 ≤ k) (heven : Even k)
    {u : ℝ} (hu : 0 ≤ u) :
    uniformProb (fun b : Fin k → Bool => u+Real.sqrt (delta/k)*rademacherSum b ≤ 1+delta) ≤
      (1/2)*Real.exp (4*Real.sqrt delta+(1-u^2)/Real.sqrt (2*Real.pi*delta)) := by
  have h := perturbed_tail_normalized hk heven hu
  have hd : 0 ≤ delta := by rw [delta_value]; norm_num
  have hnoise : Real.sqrt (delta/k) = (1/2048)/Real.sqrt (k:ℝ) := by
    rw [Real.sqrt_div hd, sqrt_delta_value]
  rw [perturbed_exponent_identity]
  simp_rw [hnoise, delta_value]
  convert h using 1
  congr 1
  funext b
  congr 1
  ring

/-- All four conclusions of the paper's Lemma 2.2. -/
theorem lemma_2_2 {k : ℕ} (hk : 2 ≤ k) (heven : Even k) :
    (uniformMean (fun b : Fin k → Bool => |rademacherSum b|) ≤ (4/5)*Real.sqrt k) ∧
    (∀ t : ℝ, uniformMean (fun b : Fin k → Bool => Real.exp (t*rademacherSum b/Real.sqrt k)) ≤
      Real.exp (t^2/2)) ∧
    (∀ t : ℝ, uniformProb (fun b : Fin k → Bool => rademacherSum b ≤ t*Real.sqrt k-1) ≤
      (1/2)*Real.exp (Real.sqrt (2/Real.pi)*t)) ∧
    (2^24 ≤ k → ∀ u : ℝ, 0 ≤ u →
      uniformProb (fun b : Fin k → Bool => u+Real.sqrt (delta/k)*rademacherSum b ≤ 1+delta) ≤
        (1/2)*Real.exp (4*Real.sqrt delta+(1-u^2)/Real.sqrt (2*Real.pi*delta))) := by
  exact ⟨lemma_2_2_a hk heven, lemma_2_2_b (by omega), lemma_2_2_c hk heven,
    fun hk' _ hu => lemma_2_2_d hk' heven hu⟩

end Stoc393

end
/- END original module: Stoc393.PerturbedTail -/

/- BEGIN original module: Stoc393.IndependentNoise -/
section

/-! Finite independence and one-coordinate estimates for the noise in Lemma 2.3. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem uniformProb_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProb (fun _ : Ω => True) = 1 := by
  rw [uniformProb_eq_indicator_mean]
  simp only [ite_true]
  exact uniformMean_const 1

theorem uniformProb_pi {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (P : ι → β → Prop) :
    uniformProb (fun b : ι → β => ∀ i, P i (b i)) = ∏ i, uniformProb (P i) := by
  classical
  have hp (b : ι → β) : (if ∀ i, P i (b i) then (1:ℝ) else 0) =
      ∏ i, (if P i (b i) then 1 else 0) := by
    by_cases h : ∀ i, P i (b i)
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i,hi⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [uniformProb_eq_indicator_mean]
  simp_rw [hp]
  rw [uniformMean_pi_product (fun i x => if P i x then (1:ℝ) else 0)]
  simp_rw [← uniformProb_eq_indicator_mean]

theorem uniformProb_pi_on {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (s : Finset ι) (P : ι → β → Prop) :
    uniformProb (fun b : ι → β => ∀ i ∈ s, P i (b i)) = ∏ i ∈ s, uniformProb (P i) := by
  classical
  rw [uniformProb_pi (fun i x => i ∈ s → P i x)]
  calc
    (∏ i, uniformProb (fun x => i ∈ s → P i x)) =
        ∏ i ∈ s, uniformProb (fun x => i ∈ s → P i x) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ s)
      intro i _ hi
      simp only [hi, false_implies]
      exact uniformProb_true
    _ = ∏ i ∈ s, uniformProb (P i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [hi,true_implies]

theorem absolute_noise_symmetry (k : ℕ) (z D : ℝ) :
    uniformProb (fun b : Fin k → Bool => |z+rademacherSum b| ≤ D) =
      uniformProb (fun b : Fin k → Bool => |(|z|)+rademacherSum b| ≤ D) := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
  · have h := uniformProb_equiv (negateBits k)
      (fun b : Fin k → Bool => |z+rademacherSum b| ≤ D)
    rw [← h]
    congr 1
    funext b
    rw [rademacherSum_negate,abs_of_neg (lt_of_not_ge hz)]
    have hid : z+-rademacherSum b = -(-z+rademacherSum b) := by ring
    rw [hid, abs_neg]

theorem noise_scale_identity {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n) :
    Real.sqrt (delta/k) = 1/Real.sqrt (n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 < delta := by rw [delta_value]; norm_num
  have hid : delta/(k:ℝ) = 1/(n:ℝ) := by
    rw [hk]
    field_simp
  rw [hid, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]

theorem coordinate_noise_bound {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n)
    (hkbig : 2^24 ≤ k) (heven : Even k) (z : ℝ) :
    uniformProb (fun b : Fin k → Bool => |z+rademacherSum b| ≤ (1+delta)*Real.sqrt n) ≤
      (1/2)*Real.exp (4*Real.sqrt delta+(1-z^2/(n:ℝ))/Real.sqrt (2*Real.pi*delta)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hspos := Real.sqrt_pos.mpr hnR
  rw [absolute_noise_symmetry k z]
  have hp := uniformProb_mono
    (Q := fun b : Fin k → Bool => |z|/Real.sqrt n+Real.sqrt (delta/k)*rademacherSum b ≤ 1+delta)
    (fun b (hb : |(|z|)+rademacherSum b| ≤ (1+delta)*Real.sqrt n) => by
      rw [noise_scale_identity hn hk]
      have h := (le_abs_self (|z|+rademacherSum b)).trans hb
      have hd := (div_le_iff₀ hspos).mpr h
      simpa only [add_div, one_div_mul_eq_div] using hd)
  have ht := lemma_2_2_d hkbig heven (show 0 ≤ |z|/Real.sqrt (n:ℝ) by positivity)
  have hid : (|z|/Real.sqrt (n:ℝ))^2 = z^2/(n:ℝ) := by
    rw [div_pow, sq_abs, Real.sq_sqrt hnR.le]
  rw [hid] at ht
  exact hp.trans ht

theorem coordinate_noise_bound_exact {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n)
    (hkbig : 2^24 ≤ k) (heven : Even k) (z : ℝ) :
    uniformProb (fun b : Fin k → Bool => |z+rademacherSum b| ≤ (1+delta)*Real.sqrt n) ≤
      (1/2)*Real.exp (1/512+1024*signTailConstant*(1-z^2/(n:ℝ))) := by
  have h := coordinate_noise_bound hn hk hkbig heven z
  have hid := perturbed_exponent_identity (|z|/Real.sqrt (n:ℝ))
  rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)] at hid
  rwa [hid] at h

end Stoc393

end
/- END original module: Stoc393.IndependentNoise -/

/- BEGIN original module: Stoc393.NoiseSmallBall -/
section

/-! Independent binomial noise and the product estimate used in Lemma 2.3. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

def noiseCount (n : ℕ) : ℕ := n/2^22

theorem noiseCount_properties {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n) :
    (noiseCount n:ℝ) = delta*n ∧ 2^24 ≤ noiseCount n ∧ Even (noiseCount n) := by
  obtain ⟨m,rfl⟩ := hp
  have hm : 50 ≤ m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hn
  have heq : (2:ℕ)^m = 2^(m-22)*2^22 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 22 ≤ m)]
  have hk : noiseCount (2^m) = 2^(m-22) := by
    unfold noiseCount
    conv_lhs => rw [heq]
    simp
  rw [hk]
  refine ⟨?_,?_,?_⟩
  · have hc : (((2:ℕ)^m):ℝ) = (((2:ℕ)^(m-22)):ℝ)*4194304 := by exact_mod_cast heq
    rw [delta_value]
    push_cast at hc ⊢
    linarith
  · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
  · refine ⟨2^(m-23),?_⟩
    rw [show m-22 = (m-23)+1 by omega, pow_succ]
    omega

noncomputable def noiseSmallBallProbability {n k : ℕ} (z : Fin n → ℝ) : ℝ :=
  uniformProb (fun b : Fin n → Fin k → Bool =>
    ‖fun i => z i+rademacherSum (b i)‖ ≤ (1+delta)*Real.sqrt n)

theorem noiseSmallBallProbability_eq {n k : ℕ} (z : Fin n → ℝ) :
    noiseSmallBallProbability (k := k) z =
      uniformProb (fun b : Fin n → Fin k → Bool =>
        ∀ i, |z i+rademacherSum (b i)| ≤ (1+delta)*Real.sqrt n) := by
  have hD : 0 ≤ (1+delta)*Real.sqrt (n:ℝ) := by rw [delta_value]; positivity
  unfold noiseSmallBallProbability
  congr 1
  funext b
  apply propext
  simpa only [Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg (x := fun i => z i+rademacherSum (b i)) hD)

theorem noiseSmallBall_product_bound {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n)
    (hkbig : 2^24 ≤ k) (heven : Even k) (z : Fin n → ℝ) (s : Finset (Fin n)) :
    noiseSmallBallProbability (k := k) z ≤
      (1/2:ℝ)^s.card * Real.exp (∑ i ∈ s, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)))) := by
  classical
  rw [noiseSmallBallProbability_eq]
  have hrestrict := uniformProb_mono (P := fun b : Fin n → Fin k → Bool =>
    ∀ i, |z i+rademacherSum (b i)| ≤ (1+delta)*Real.sqrt n)
    (Q := fun b => ∀ i ∈ s, |z i+rademacherSum (b i)| ≤ (1+delta)*Real.sqrt n)
    (fun b hb i _ => hb i)
  rw [uniformProb_pi_on s (fun i b => |z i+rademacherSum b| ≤ (1+delta)*Real.sqrt n)] at hrestrict
  have hprod := Finset.prod_le_prod₀
    (fun i (_ : i ∈ s) => uniformProb_nonneg
      (fun b : Fin k → Bool => |z i+rademacherSum b| ≤ (1+delta)*Real.sqrt n))
    (fun i (_ : i ∈ s) => coordinate_noise_bound_exact hn hk hkbig heven (z i))
  have h := hrestrict.trans hprod
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,← Real.exp_sum] using h

theorem noiseSmallBall_bound_a {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n)
    (hkbig : 2^24 ≤ k) (heven : Even k) (z : Fin n → ℝ)
    (henergy : (∑ i, z i^2) = (1-delta)*(n:ℝ)^2) :
    noiseSmallBallProbability (k := k) z ≤ (2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320) := by
  classical
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h := noiseSmallBall_product_bound hn hk hkbig heven z Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hsum : (∑ i : Fin n, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)))) =
      (n:ℝ)*(4+signTailConstant/2)/2048 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_div]
    rw [henergy,delta_value]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    field_simp
    ring
  rw [hsum] at h
  have hC := signTailConstant_bounds.2
  have hlog : (4+signTailConstant/2)/2048 ≤ Real.log 2/320 := by
    linarith [Real.log_two_gt_d9]
  have hscale := mul_le_mul_of_nonneg_left hlog hnR.le
  have hE : Real.exp ((n:ℝ)*(4+signTailConstant/2)/2048) ≤ (2:ℝ)^((n:ℝ)/320) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hhalf : (1/2:ℝ)^n = (2:ℝ)^(-(n:ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    simp
  rw [hhalf] at h
  exact h.trans (mul_le_mul_of_nonneg_left hE (by positivity))

theorem noiseSmallBall_bound_b {n k : ℕ} (hn : 0 < n) (hk : (k:ℝ) = delta*n)
    (hkbig : 2^24 ≤ k) (heven : Even k) (z : Fin n → ℝ)
    (henergy : (∑ i, z i^2) = (1-delta)*(n:ℝ)^2)
    (hl1 : (∑ i, |z i|) ≤ (99/100)*(n:ℝ)*Real.sqrt n) :
    noiseSmallBallProbability (k := k) z ≤ (2:ℝ)^(-3*(n:ℝ)) := by
  classical
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnne := ne_of_gt hnR
  let s := Finset.univ.filter (fun i : Fin n => Real.sqrt (n:ℝ) < |z i|)
  have h := noiseSmallBall_product_bound hn hk hkbig heven z s
  have hlex : (∑ i, |z i|) ≤ (1-(1:ℝ)/100)*(n:ℝ)*Real.sqrt n := by
    convert hl1 using 1
    norm_num
  have hex := excess_energy_from_l1 z (δ := delta) (η := (1:ℝ)/100)
    (Real.sqrt_nonneg _) (Real.sq_sqrt hnR.le) henergy hlex
  have hδ : (n:ℝ)^2/200 ≤ ((1:ℝ)/100-delta)*(n:ℝ)^2 := by
    rw [delta_value]
    nlinarith [sq_nonneg (n:ℝ)]
  have hexcess : (n:ℝ)^2/200 ≤ ∑ i ∈ s, (z i^2-(n:ℝ)) := hδ.trans hex
  have hsum : (∑ i ∈ s, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)))) =
      (s.card:ℝ)/512-(1024*signTailConstant/(n:ℝ))*(∑ i ∈ s, (z i^2-(n:ℝ))) := by
    have hterm (i : Fin n) : 1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)) =
        1/512-(1024*signTailConstant/(n:ℝ))*(z i^2-(n:ℝ)) := by
      field_simp
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    ring
  have hcard : (s.card:ℝ) ≤ n := by
    have hc : s.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ s
    exact_mod_cast hc
  have hC := signTailConstant_bounds
  have hmul := mul_le_mul_of_nonneg_left hexcess
    (show 0 ≤ 1024*signTailConstant/(n:ℝ) by
      have hc : 0 ≤ signTailConstant := by linarith [hC.1]
      positivity)
  have hid : (1024*signTailConstant/(n:ℝ))*((n:ℝ)^2/200) = (128/25)*signTailConstant*n := by
    field_simp
    ring
  rw [hid] at hmul
  have hcoef : (1:ℝ)/512-(128/25)*signTailConstant ≤ -3*Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  have hscaled := mul_le_mul_of_nonneg_right hcoef hnR.le
  have hE : (∑ i ∈ s, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)))) ≤
      Real.log 2*(-3*(n:ℝ)) := by
    rw [hsum]
    nlinarith
  have hhalf : (1/2:ℝ)^s.card ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnohalf : noiseSmallBallProbability (k := k) z ≤
      Real.exp (∑ i ∈ s, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ)))) := by
    have hpos := Real.exp_pos (∑ i ∈ s, (1/512+1024*signTailConstant*(1-z i^2/(n:ℝ))))
    nlinarith
  rw [Real.rpow_def_of_pos (by norm_num)]
  exact hnohalf.trans (Real.exp_le_exp.mpr hE)

/-- Both conclusions of Lemma 2.3, using independent uniform sign coordinates. -/
theorem lemma_2_3 {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n)
    (z : Fin n → ℝ) (henergy : (∑ i, z i^2) = (1-delta)*(n:ℝ)^2) :
    noiseSmallBallProbability (k := noiseCount n) z ≤ (2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320) ∧
    ((∑ i, |z i|) ≤ (99/100)*(n:ℝ)*Real.sqrt n →
      noiseSmallBallProbability (k := noiseCount n) z ≤ (2:ℝ)^(-3*(n:ℝ))) := by
  obtain ⟨hk,hkbig,heven⟩ := noiseCount_properties hp hn
  have hnpos : 0 < n := by omega
  exact ⟨noiseSmallBall_bound_a hnpos hk hkbig heven z henergy,
    noiseSmallBall_bound_b hnpos hk hkbig heven z henergy⟩

end Stoc393

end
/- END original module: Stoc393.NoiseSmallBall -/

/- BEGIN original module: Stoc393.ConvexCubeTail -/
section

/-! Concentration consequences of the verified Talagrand moment bound. -/
set_option autoImplicit false
namespace Stoc393

theorem uniformProb_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    uniformProb (fun x => ¬ P x) = 1-uniformProb P := by
  classical
  have hpoint (x : Ω) : (if P x then (1:ℝ) else 0)+(if ¬ P x then 1 else 0) = 1 := by
    by_cases h : P x <;> simp [h]
  have h := congrArg (fun f : Ω → ℝ => uniformMean f) (funext hpoint)
  rw [uniformMean_add, uniformMean_const,
    ← uniformProb_eq_indicator_mean, ← uniformProb_eq_indicator_mean] at h
  linarith

theorem uniform_sublevel_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) :
    1-uniformMean f/a ≤ uniformProb (fun x => f x ≤ a) := by
  have hmarkov := uniform_markov hf ha
  have hmono := uniformProb_mono (P := fun x => ¬ f x ≤ a) (Q := fun x => a ≤ f x)
    (fun x hx => (lt_of_not_ge hx).le)
  rw [uniformProb_compl] at hmono
  linarith

theorem cube_distance_tail {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hp : 0 < cubeProbability K)
    {r : ℝ} (hr : 0 ≤ r) :
    uniformProb (fun b : Fin n → Bool => r ≤ Metric.infDist (cubePoint b) K) ≤
      Real.exp (-r^2/16)/cubeProbability K := by
  have hmono := uniformProb_mono
    (P := fun b : Fin n → Bool => r ≤ Metric.infDist (cubePoint b) K)
    (Q := fun b => Real.exp (r^2/16) ≤ Real.exp (Metric.infDist (cubePoint b) K^2/16))
    (fun b hb => by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hb 2) (by norm_num))
  have hmarkov := uniform_markov
    (fun b : Fin n → Bool => Real.exp_nonneg (Metric.infDist (cubePoint b) K^2/16))
    (Real.exp_pos (r^2/16))
  have hmoment := lemma_2_1 n K hclosed hconvex hp
  have hdiv := div_le_div_of_nonneg_right hmoment (Real.exp_nonneg (r^2/16))
  have h := hmono.trans (hmarkov.trans hdiv)
  have hid : (1/cubeProbability K)/Real.exp (r^2/16) = Real.exp (-r^2/16)/cubeProbability K := by
    rw [show -r^2/16 = -(r^2/16) by ring, Real.exp_neg]
    field_simp
  rwa [hid] at h

end Stoc393

end
/- END original module: Stoc393.ConvexCubeTail -/

/- BEGIN original module: Stoc393.SignedCube -/
section

/-! Multiplying independent signs by fixed signs preserves the uniform cube. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def signedBitsEquiv {m : ℕ} (a : Fin m → ℝ) : (Fin m → Bool) ≃ (Fin m → Bool) := by
  classical
  exact {
    toFun := fun b j => if a j = 1 then b j else !(b j)
    invFun := fun b j => if a j = 1 then b j else !(b j)
    left_inv := by intro b; funext j; by_cases h : a j = 1 <;> simp [h]
    right_inv := by intro b; funext j; by_cases h : a j = 1 <;> simp [h]
  }

theorem signedBits_sum {m : ℕ} (a : Fin m → ℝ) (ha : IsSigning a) (b : Fin m → Bool) :
    rademacherSum (signedBitsEquiv a b) = ∑ j, a j*bitSign (b j) := by
  classical
  unfold rademacherSum
  apply Finset.sum_congr rfl
  intro j _
  rcases ha j with h|h
  · simp [signedBitsEquiv,h]
  · norm_num [signedBitsEquiv,h,bitSign_not]

theorem uniformMean_signed_sum {m : ℕ} (a : Fin m → ℝ) (ha : IsSigning a) (f : ℝ → ℝ) :
    uniformMean (fun b : Fin m → Bool => f (∑ j, a j*bitSign (b j))) =
      uniformMean (fun b : Fin m → Bool => f (rademacherSum b)) := by
  have h := uniformMean_equiv (signedBitsEquiv a) (fun b => f (rademacherSum b))
  simpa only [signedBits_sum a ha] using h

theorem uniformProb_signed_sum {m : ℕ} (a : Fin m → ℝ) (ha : IsSigning a) (P : ℝ → Prop) :
    uniformProb (fun b : Fin m → Bool => P (∑ j, a j*bitSign (b j))) =
      uniformProb (fun b : Fin m → Bool => P (rademacherSum b)) := by
  have h := uniformProb_equiv (signedBitsEquiv a) (fun b => P (rademacherSum b))
  simpa only [signedBits_sum a ha] using h

theorem uniformMean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    uniformMean (fun b => ∑ i, f i b) = ∑ i, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem signing_matrix_l1_mean {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hH : ∀ i j, H i j = 1 ∨ H i j = -1) (hm : 2 ≤ m) (heven : Even m) :
    uniformMean (fun b : Fin m → Bool => ∑ i, |H.mulVec (fun j => bitSign (b j)) i|) ≤
      (4/5)*(n:ℝ)*Real.sqrt m := by
  have heq : uniformMean (fun b : Fin m → Bool => ∑ i, |H.mulVec (fun j => bitSign (b j)) i|) =
      (n:ℝ)*uniformMean (fun b : Fin m → Bool => |rademacherSum b|) := by
    rw [uniformMean_sum]
    have hrow (i : Fin n) : uniformMean (fun b : Fin m → Bool => |H.mulVec (fun j => bitSign (b j)) i|) =
        uniformMean (fun b : Fin m → Bool => |rademacherSum b|) :=
      uniformMean_signed_sum (H i) (hH i) abs
    simp_rw [hrow]
    simp
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (lemma_2_2_a hm heven) (show (0:ℝ) ≤ n by positivity)
  nlinarith

end Stoc393

end
/- END original module: Stoc393.SignedCube -/

/- BEGIN original module: Stoc393.MatrixL1Geometry -/
section

/-! The closed convex l1 sublevel set and its distance estimate in Section 2.2. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def matrixL1 {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := ∑ i, |H.mulVec (fun j => x j) i|

theorem matrixL1_nonneg {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ matrixL1 H x :=
  Finset.sum_nonneg (fun _i _ => abs_nonneg _)

theorem matrixL1_continuous {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (matrixL1 H) := by
  unfold matrixL1 Matrix.mulVec dotProduct
  fun_prop

theorem matrixL1_norm_bound {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hH : ∀ j k, (∑ i, H i j*H i k) = if j = k then (n:ℝ) else 0)
    (x : EuclideanSpace ℝ (Fin m)) : matrixL1 H x ≤ (n:ℝ)*‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1:ℝ)) (fun i => |H.mulVec (fun j => x j) i|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,sq_abs] at hcs
  rw [orthogonal_columns_energy H (n:ℝ) hH, ← EuclideanSpace.real_norm_sq_eq x] at hcs
  apply (sq_le_sq₀ (matrixL1_nonneg H x) (by positivity : 0 ≤ (n:ℝ)*‖x‖)).mp
  change (∑ i, |H.mulVec (fun j => x j) i|)^2 ≤ ((n:ℝ)*‖x‖)^2
  nlinarith

theorem matrixL1_triangle_sub {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (x y : EuclideanSpace ℝ (Fin m)) : matrixL1 H x ≤ matrixL1 H y+matrixL1 H (x-y) := by
  unfold matrixL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hid : H.mulVec (fun j => x j) i =
      H.mulVec (fun j => y j) i+H.mulVec (fun j => (x-y) j) i := by
    change H.mulVec (fun j => x j) i =
      H.mulVec (fun j => y j) i+H.mulVec ((fun j => x j)-(fun j => y j)) i
    rw [Matrix.mulVec_sub]
    simp
  rw [hid]
  exact abs_add_le _ _

theorem matrixL1_distance_bound {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hH : ∀ j k, (∑ i, H i j*H i k) = if j = k then (n:ℝ) else 0)
    (x y : EuclideanSpace ℝ (Fin m)) : matrixL1 H x ≤ matrixL1 H y+(n:ℝ)*dist x y := by
  rw [dist_eq_norm]
  exact (matrixL1_triangle_sub H x y).trans
    (add_le_add le_rfl (matrixL1_norm_bound H hH (x-y)))

theorem matrixL1_convex_combination {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (x y : EuclideanSpace ℝ (Fin m)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    matrixL1 H (a • x+b • y) ≤ a*matrixL1 H x+b*matrixL1 H y := by
  unfold matrixL1
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change |H.mulVec (a • (fun j => x j)+b • (fun j => y j)) i| ≤ _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
    abs_add_le (a*H.mulVec (fun j => x j) i) (b*H.mulVec (fun j => y j) i)

theorem matrixL1_sublevel_closed {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ) (D : ℝ) :
    IsClosed {x | matrixL1 H x ≤ D} := isClosed_le (matrixL1_continuous H) continuous_const

theorem matrixL1_sublevel_convex {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ) (D : ℝ) :
    Convex ℝ {x | matrixL1 H x ≤ D} := by
  intro x hx y hy a b ha hb hab
  change matrixL1 H (a • x+b • y) ≤ D
  have h := (matrixL1_convex_combination H x y ha hb).trans
    (add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb))
  have hid : a*D+b*D = D := by rw [← add_mul, hab, one_mul]
  rwa [hid] at h

end Stoc393

end
/- END original module: Stoc393.MatrixL1Geometry -/

/- BEGIN original module: Stoc393.ExceptionalSignings -/
section

/-! The exceptional-signing estimate in Section 2.2. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def matrixCentralSet {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin m)) := {x | matrixL1 H x ≤ (4/5)*(n:ℝ)*Real.sqrt n}

theorem matrixCentralSet_probability {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hn : 0 < n) (hm : 2 ≤ m) (heven : Even m) (hsize : (m:ℝ) = (1-delta)*n)
    (hsigns : ∀ i j, H i j = 1 ∨ H i j = -1) :
    delta/2 ≤ cubeProbability (matrixCentralSet H) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hspos := Real.sqrt_pos.mpr hnR
  have hδ : 0 ≤ 1-delta/2 := by rw [delta_value]; norm_num
  have hsqrt : Real.sqrt (m:ℝ) ≤ (1-delta/2)*Real.sqrt n := by
    apply (Real.sqrt_le_left (mul_nonneg hδ hspos.le)).mpr
    rw [mul_pow,Real.sq_sqrt hnR.le,hsize]
    have h := mul_nonneg (sq_nonneg delta) hnR.le
    nlinarith
  have hmean : uniformMean (fun b : Fin m → Bool => matrixL1 H (cubePoint b)) ≤
      (4/5)*(n:ℝ)*Real.sqrt m := signing_matrix_l1_mean H hsigns hm heven
  have hscaled := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (4/5)*(n:ℝ) by positivity)
  have hbound : uniformMean (fun b : Fin m → Bool => matrixL1 H (cubePoint b)) ≤
      (1-delta/2)*((4/5)*(n:ℝ)*Real.sqrt n) := by nlinarith
  have hA : 0 < (4/5)*(n:ℝ)*Real.sqrt n := by positivity
  have hdiv := (div_le_iff₀ hA).mpr hbound
  have hsub := uniform_sublevel_probability (fun b : Fin m → Bool => matrixL1_nonneg H (cubePoint b)) hA
  change 1-uniformMean (fun b : Fin m → Bool => matrixL1 H (cubePoint b))/
    ((4/5)*(n:ℝ)*Real.sqrt n) ≤ cubeProbability (matrixCentralSet H) at hsub
  linarith

theorem matrixL1_infDist_bound {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hH : ∀ j k, (∑ i, H i j*H i k) = if j = k then (n:ℝ) else 0)
    (hne : (matrixCentralSet H).Nonempty) (x : EuclideanSpace ℝ (Fin m)) :
    matrixL1 H x ≤ (4/5)*(n:ℝ)*Real.sqrt n+(n:ℝ)*Metric.infDist x (matrixCentralSet H) := by
  obtain ⟨y,hy,hd⟩ := (matrixL1_sublevel_closed H ((4/5)*(n:ℝ)*Real.sqrt n)).exists_infDist_eq_dist hne x
  have h := matrixL1_distance_bound H hH x y
  change matrixL1 H y ≤ (4/5)*(n:ℝ)*Real.sqrt n at hy
  change Metric.infDist x (matrixCentralSet H) = dist x y at hd
  rw [hd]
  linarith

theorem exceptional_probability_numeric {N : ℝ} (hN : (2:ℝ)^50 ≤ N) :
    Real.exp (-361*N/160000)/(delta/2) < (2:ℝ)^(-N/310) := by
  have hN0 : 0 ≤ N := by nlinarith [show (0:ℝ) < 2^50 by positivity]
  have hpow : (2:ℝ)^23 ≤ Real.exp 23 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) 23
    simpa only [← Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using h
  have hconst : (1:ℝ)/(delta/2) ≤ Real.exp 23 := by
    convert hpow using 1
    norm_num [delta_value]
  have hlogN := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le hN0
  have hstrict : Real.exp (23-361*N/160000) < (2:ℝ)^(-N/310) := by
    rw [Real.rpow_def_of_pos (by norm_num),Real.exp_lt_exp]
    nlinarith
  calc
    Real.exp (-361*N/160000)/(delta/2) = Real.exp (-361*N/160000)*(1/(delta/2)) := by ring
    _ ≤ Real.exp (-361*N/160000)*Real.exp 23 :=
      mul_le_mul_of_nonneg_left hconst (Real.exp_nonneg _)
    _ = Real.exp (23-361*N/160000) := by rw [← Real.exp_add]; congr 1; ring
    _ < (2:ℝ)^(-N/310) := hstrict

/-- The unnumbered exceptional-signing claim in the proof of Theorem 1.1. -/
theorem exceptional_signings_bound {n m : ℕ} (H : Matrix (Fin n) (Fin m) ℝ)
    (hn : 2^50 ≤ n) (hm : 2 ≤ m) (heven : Even m) (hsize : (m:ℝ) = (1-delta)*n)
    (hsigns : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH : ∀ j k, (∑ i, H i j*H i k) = if j = k then (n:ℝ) else 0) :
    uniformProb (fun b : Fin m → Bool =>
      (99/100)*(n:ℝ)*Real.sqrt n < ∑ i, |H.mulVec (fun j => bitSign (b j)) i|) <
      (2:ℝ)^(-(n:ℝ)/310) := by
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hδ : 0 < delta/2 := by rw [delta_value]; norm_num
  have hp := matrixCentralSet_probability H hnpos hm heven hsize hsigns
  have hppos : 0 < cubeProbability (matrixCentralSet H) := hδ.trans_le hp
  have hne := cubeProbability_pos_nonempty hppos
  have hmono := uniformProb_mono
    (P := fun b : Fin m → Bool => (99/100)*(n:ℝ)*Real.sqrt n < matrixL1 H (cubePoint b))
    (Q := fun b => (19/100)*Real.sqrt n ≤ Metric.infDist (cubePoint b) (matrixCentralSet H))
    (fun b hb => by
      have h := matrixL1_infDist_bound H hH hne (cubePoint b)
      by_contra hd
      have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hd) hnR
      nlinarith)
  have ht := cube_distance_tail (matrixL1_sublevel_closed H _) (matrixL1_sublevel_convex H _)
    hppos (show 0 ≤ (19/100)*Real.sqrt (n:ℝ) by positivity)
  have hdiv := div_le_div_of_nonneg_left
    (Real.exp_nonneg (-((19/100)*Real.sqrt (n:ℝ))^2/16)) hδ hp
  have h := hmono.trans (ht.trans hdiv)
  have heq : -((19/100)*Real.sqrt (n:ℝ))^2/16 = -361*(n:ℝ)/160000 := by
    rw [mul_pow,Real.sq_sqrt hnR.le]
    ring
  rw [heq] at h
  exact h.trans_lt (exceptional_probability_numeric (by exact_mod_cast hn))

end Stoc393

end
/- END original module: Stoc393.ExceptionalSignings -/

/- BEGIN original module: Stoc393.ColumnRestriction -/
section

/-! Restricting uniform signs to a column set and enumerating that set. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem uniformMean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℝ) :
    uniformMean (fun p : α × β => f p.1) = uniformMean f := by
  have hα : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.mul_sum,Fintype.card_prod,Nat.cast_mul]
  field_simp

theorem uniformProb_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (P : α → Prop) :
    uniformProb (fun p : α × β => P p.1) = uniformProb P := by
  classical
  simp only [uniformProb_eq_indicator_mean]
  exact uniformMean_prod_fst (fun a => if P a then 1 else 0)

noncomputable def columnEnum {n : ℕ} (s : Finset (Fin n)) (j : Fin s.card) : Fin n :=
  (s.equivFin.symm j).val

theorem columnEnum_mem {n : ℕ} (s : Finset (Fin n)) (j : Fin s.card) : columnEnum s j ∈ s :=
  (s.equivFin.symm j).property

theorem columnEnum_injective {n : ℕ} (s : Finset (Fin n)) : Function.Injective (columnEnum s) := by
  intro i j h
  exact s.equivFin.symm.injective (Subtype.ext h)

theorem sum_columnEnum {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ j : Fin s.card, f (columnEnum s j)) = ∑ j ∈ s, f j := by
  unfold columnEnum
  exact (s.equivFin.symm.sum_comp (fun j : s => f j.val)).trans (Finset.sum_coe_sort s f)

theorem uniformProb_columnRestriction {n : ℕ} (s : Finset (Fin n))
    (P : (Fin s.card → Bool) → Prop) :
    uniformProb (fun b : Fin n → Bool => P (fun j => b (columnEnum s j))) = uniformProb P := by
  classical
  have hsplit := uniformProb_equiv
    (Equiv.piEquivPiSubtypeProd (fun j : Fin n => j ∈ s) (fun _ => Bool))
    (fun p => P (fun j => p.1 (s.equivFin.symm j)))
  have hfst := uniformProb_prod_fst (β := ({j : Fin n // j ∉ s} → Bool))
    (fun b : s → Bool => P (fun j => b (s.equivFin.symm j)))
  have hreindex := uniformProb_equiv (Equiv.arrowCongr s.equivFin (Equiv.refl Bool)) P
  exact hsplit.trans (hfst.trans hreindex)

end Stoc393

end
/- END original module: Stoc393.ColumnRestriction -/

/- BEGIN original module: Stoc393.RetainedColumns -/
section

/-! The unchanged columns in the random Hadamard perturbation. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def retainedMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) : Matrix (Fin n) (Fin Cᶜ.card) ℝ :=
  fun i j => H i (columnEnum Cᶜ j)

noncomputable def retainedVector {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (b : Fin n → Bool) : Fin n → ℝ :=
  fun i => ∑ j ∈ Cᶜ, H i j*bitSign (b j)

theorem retainedMatrix_action {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (b : Fin n → Bool) :
    (retainedMatrix H C).mulVec (fun j => bitSign (b (columnEnum Cᶜ j))) = retainedVector H C b := by
  funext i
  exact sum_columnEnum Cᶜ (fun j => H i j*bitSign (b j))

theorem retainedMatrix_orthogonal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : IsHadamard H) (C : Finset (Fin n)) :
    ∀ j k, (∑ i, retainedMatrix H C i j*retainedMatrix H C i k) =
      if j = k then (n:ℝ) else 0 := by
  intro j k
  simpa only [retainedMatrix,(columnEnum_injective Cᶜ).eq_iff] using
    hH.2 (columnEnum Cᶜ j) (columnEnum Cᶜ k)

theorem retained_size {n : ℕ} (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) :
    (Cᶜ.card:ℝ) = (1-delta)*n := by
  have hle : C.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ C
  rw [Finset.card_compl,Fintype.card_fin,Nat.cast_sub hle,hC]
  ring

theorem retained_dimension_properties {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n)
    (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) :
    C.card = noiseCount n ∧ 2 ≤ Cᶜ.card ∧ Even Cᶜ.card := by
  obtain ⟨hk,hkbig,hkeven⟩ := noiseCount_properties hp hn
  have hcard : C.card = noiseCount n := by exact_mod_cast (hC.trans hk.symm)
  have hnreal : (n:ℝ) = 4194304*(C.card:ℝ) := by rw [delta_value] at hC; linarith
  have hnnat : n = 4194304*C.card := by exact_mod_cast hnreal
  have hcomp : Cᶜ.card = 4194303*C.card := by
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  have hcpos : 2 ≤ C.card := by rw [hcard]; omega
  have hceven : Even C.card := hcard.symm ▸ hkeven
  refine ⟨hcard,?_,?_⟩
  · rw [hcomp]
    omega
  · obtain ⟨q,hq⟩ := hceven
    refine ⟨4194303*q,?_⟩
    rw [hcomp,hq]
    omega

theorem retainedVector_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : IsHadamard H) (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) (b : Fin n → Bool) :
    (∑ i, retainedVector H C b i^2) = (1-delta)*(n:ℝ)^2 := by
  have h := orthogonal_columns_signing_energy (retainedMatrix H C) (n:ℝ)
    (retainedMatrix_orthogonal H hH C)
    (show IsSigning (fun j => bitSign (b (columnEnum Cᶜ j))) from fun j => bitSign_isSign _)
  rw [retainedMatrix_action,retained_size C hC] at h
  nlinarith

theorem retained_exceptional_probability {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : IsHadamard H)
    (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) :
    uniformProb (fun b : Fin n → Bool =>
      (99/100)*(n:ℝ)*Real.sqrt n < ∑ i, |retainedVector H C b i|) < (2:ℝ)^(-(n:ℝ)/310) := by
  obtain ⟨_,hm,heven⟩ := retained_dimension_properties hp hn C hC
  have h := exceptional_signings_bound (retainedMatrix H C) hn hm heven (retained_size C hC)
    (fun i j => hH.1 i (columnEnum Cᶜ j)) (retainedMatrix_orthogonal H hH C)
  have hrestrict := uniformProb_columnRestriction Cᶜ
    (fun u => (99/100)*(n:ℝ)*Real.sqrt n < ∑ i, |(retainedMatrix H C).mulVec (fun j => bitSign (u j)) i|)
  simp only [retainedMatrix_action] at hrestrict
  rw [hrestrict]
  exact h

end Stoc393

end
/- END original module: Stoc393.RetainedColumns -/

/- BEGIN original module: Stoc393.ReplacementNoise -/
section

/-! The exact distribution of the random replaced columns for a fixed signing. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem replaceColumns_action {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (R : ReplacementBits C) (b : Fin n → Bool) (i : Fin n) :
    (replaceColumns H C R).mulVec (fun j => bitSign (b j)) i =
      retainedVector H C b i+∑ j : C, bitSign (R i j)*bitSign (b j) := by
  classical
  let f : Fin n → ℝ := fun j => replaceColumns H C R i j*bitSign (b j)
  have hs := Finset.sum_add_sum_compl C f
  have htrue : (∑ j ∈ C, f j) = ∑ j : C, bitSign (R i j)*bitSign (b j) := by
    rw [← Finset.sum_coe_sort C f]
    apply Finset.sum_congr rfl
    intro j _
    simp [f,replaceColumns,j.property]
  have hfalse : (∑ j ∈ Cᶜ, f j) = retainedVector H C b i := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f,replaceColumns,Finset.mem_compl.mp hj]
  rw [htrue,hfalse] at hs
  change (∑ j, f j) = _
  linarith

theorem replacement_row_distribution {n : ℕ} (C : Finset (Fin n)) (b : Fin n → Bool)
    (P : ℝ → Prop) :
    uniformProb (fun r : C → Bool => P (∑ j : C, bitSign (r j)*bitSign (b j))) =
      uniformProb (fun r : Fin C.card → Bool => P (rademacherSum r)) := by
  classical
  let e := Equiv.arrowCongr C.equivFin (Equiv.refl Bool)
  let a : Fin C.card → ℝ := fun j => bitSign (b (columnEnum C j))
  have h := uniformProb_equiv e (fun r => P (∑ j, a j*bitSign (r j)))
  have heq (r : C → Bool) : (∑ j : Fin C.card, a j*bitSign (e r j)) =
      ∑ j : C, bitSign (r j)*bitSign (b j) := by
    change (∑ j : Fin C.card,
      bitSign (b (C.equivFin.symm j))*bitSign (r (C.equivFin.symm j))) = _
    rw [C.equivFin.symm.sum_comp (fun j : C => bitSign (b j)*bitSign (r j))]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq] at h
  exact h.trans (uniformProb_signed_sum a (fun j => bitSign_isSign _) P)

def replacementBadEvent {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (C : Finset (Fin n))
    (R : ReplacementBits C) (b : Fin n → Bool) : Prop :=
  ‖(replaceColumns H C R).mulVec (fun j => bitSign (b j))‖ ≤ (1+delta)*Real.sqrt n

noncomputable def replacementBadProbability {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (b : Fin n → Bool) : ℝ := uniformProb (fun R => replacementBadEvent H C R b)

theorem replacementBadProbability_eq_noise {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (b : Fin n → Bool) :
    replacementBadProbability H C b = noiseSmallBallProbability (k := C.card) (retainedVector H C b) := by
  classical
  have hD : 0 ≤ (1+delta)*Real.sqrt (n:ℝ) := by rw [delta_value]; positivity
  have hevent (R : ReplacementBits C) : replacementBadEvent H C R b ↔
      ∀ i, |retainedVector H C b i+∑ j : C, bitSign (R i j)*bitSign (b j)| ≤ (1+delta)*Real.sqrt n := by
    rw [replacementBadEvent,pi_norm_le_iff_of_nonneg hD]
    simp only [Real.norm_eq_abs,replaceColumns_action]
  unfold replacementBadProbability
  simp_rw [hevent]
  rw [uniformProb_pi (β := C → Bool) (fun i r => |retainedVector H C b i+∑ j : C, bitSign (r j)*bitSign (b j)| ≤
    (1+delta)*Real.sqrt n),noiseSmallBallProbability_eq,
    uniformProb_pi (β := Fin C.card → Bool) (fun i r => |retainedVector H C b i+rademacherSum r| ≤ (1+delta)*Real.sqrt n)]
  apply Finset.prod_congr rfl
  intro i _
  exact replacement_row_distribution C b (fun w => |retainedVector H C b i+w| ≤ (1+delta)*Real.sqrt n)

theorem replacementBadProbability_bounds {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : IsHadamard H)
    (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) (b : Fin n → Bool) :
    replacementBadProbability H C b ≤ (2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320) ∧
    ((∑ i, |retainedVector H C b i|) ≤ (99/100)*(n:ℝ)*Real.sqrt n →
      replacementBadProbability H C b ≤ (2:ℝ)^(-3*(n:ℝ))) := by
  have h := lemma_2_3 hp hn (retainedVector H C b) (retainedVector_energy H hH C hC b)
  have hcard := (retained_dimension_properties hp hn C hC).1
  rw [replacementBadProbability_eq_noise,hcard]
  exact h

end Stoc393

end
/- END original module: Stoc393.ReplacementNoise -/

/- BEGIN original module: Stoc393.FiniteUnionBound -/
section

/-! Exact finite union bounds with two classes of signings. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem uniform_union_bound {Ω B : Type*} [Fintype Ω] [Fintype B]
    (E : Ω → B → Prop) :
    uniformProb (fun ω => ∃ b, E ω b) ≤ ∑ b, uniformProb (fun ω => E ω b) := by
  classical
  have hpoint (ω : Ω) : (if ∃ b, E ω b then (1:ℝ) else 0) ≤
      ∑ b, (if E ω b then 1 else 0) := by
    by_cases h : ∃ b, E ω b
    · rw [ite_eq_left h]
      obtain ⟨b,hb⟩ := h
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun b => if E ω b then (1:ℝ) else 0)
        (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ b)
      simpa only [hb,ite_true] using hs
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)
  have h := uniformMean_mono hpoint
  rw [uniformMean_sum] at h
  simpa only [← uniformProb_eq_indicator_mean] using h

theorem uniform_union_bound_two_classes {Ω B : Type*} [Fintype Ω] [Fintype B] [Nonempty B]
    (E : Ω → B → Prop) (X : B → Prop) {pg pb : ℝ} (hg : 0 ≤ pg)
    (hall : ∀ b, uniformProb (fun ω => E ω b) ≤ pb)
    (hgood : ∀ b, ¬ X b → uniformProb (fun ω => E ω b) ≤ pg) :
    uniformProb (fun ω => ∃ b, E ω b) ≤ (Fintype.card B:ℝ)*(pg+pb*uniformProb X) := by
  classical
  have hpoint (b : B) : uniformProb (fun ω => E ω b) ≤ pg+pb*(if X b then 1 else 0) := by
    by_cases h : X b
    · simp only [h,ite_true,mul_one]
      linarith [hall b]
    · simpa only [h,ite_false,mul_zero,add_zero] using hgood b h
  have hmean := uniformMean_mono hpoint
  rw [uniformMean_add,uniformMean_const,uniformMean_const_mul,
    ← uniformProb_eq_indicator_mean] at hmean
  have hcard : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hsum := (div_le_iff₀ hcard).mp hmean
  have h := (uniform_union_bound E).trans hsum
  simpa only [mul_comm] using h

theorem final_union_bound_numeric {n : ℕ} (hn : 2^50 ≤ n) :
    (2:ℝ)^n*((2:ℝ)^(-3*(n:ℝ))+
      ((2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320))*(2:ℝ)^(-(n:ℝ)/310)) <
      (2:ℝ)^(-(n:ℝ)/20000) := by
  have hnR : (2:ℝ)^50 ≤ n := by exact_mod_cast hn
  have hcombine : (2:ℝ)^n*((2:ℝ)^(-3*(n:ℝ))+
      ((2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320))*(2:ℝ)^(-(n:ℝ)/310)) =
      (2:ℝ)^(-2*(n:ℝ))+(2:ℝ)^(-(n:ℝ)/9920) := by
    rw [mul_add,← Real.rpow_natCast]
    simp only [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1 <;> congr 1 <;> ring
  rw [hcombine]
  have hfirst := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (show -2*(n:ℝ) ≤ -(n:ℝ)/20000-1 by nlinarith)
  have hsecond := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (show -(n:ℝ)/9920 < -(n:ℝ)/20000-1 by nlinarith)
  have hhalf : (2:ℝ)^(-(n:ℝ)/20000-1) = (1/2)*(2:ℝ)^(-(n:ℝ)/20000) := by
    rw [Real.rpow_sub (by norm_num),Real.rpow_one]
    ring
  rw [hhalf] at hfirst hsecond
  linarith

end Stoc393

end
/- END original module: Stoc393.FiniteUnionBound -/

/- BEGIN original module: Stoc393.LowerBound -/
section

/-! The lower-bound theorem for random replacement of Hadamard columns. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem replacement_failure_probability {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : IsHadamard H)
    (C : Finset (Fin n)) (hC : (C.card:ℝ) = delta*n) :
    uniformProb (fun R : ReplacementBits C => ∃ b : Fin n → Bool, replacementBadEvent H C R b) <
      (2:ℝ)^(-(n:ℝ)/20000) := by
  let X : (Fin n → Bool) → Prop := fun b =>
    (99/100)*(n:ℝ)*Real.sqrt n < ∑ i, |retainedVector H C b i|
  have hall (b : Fin n → Bool) : uniformProb (fun R => replacementBadEvent H C R b) ≤
      (2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320) :=
    (replacementBadProbability_bounds hp hn H hH C hC b).1
  have hgood (b : Fin n → Bool) (hb : ¬ X b) :
      uniformProb (fun R => replacementBadEvent H C R b) ≤ (2:ℝ)^(-3*(n:ℝ)) :=
    (replacementBadProbability_bounds hp hn H hH C hC b).2 (le_of_not_gt hb)
  have h := uniform_union_bound_two_classes (replacementBadEvent H C) X
    (show 0 ≤ (2:ℝ)^(-3*(n:ℝ)) by positivity) hall hgood
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at h
  have hX : uniformProb X ≤ (2:ℝ)^(-(n:ℝ)/310) :=
    (retained_exceptional_probability hp hn H hH C hC).le
  have hinner := mul_le_mul_of_nonneg_left hX
    (show 0 ≤ (2:ℝ)^(-(n:ℝ))*(2:ℝ)^((n:ℝ)/320) by positivity)
  have houter := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ((2:ℝ)^(-3*(n:ℝ)))) hinner)
    (show 0 ≤ (2:ℝ)^n by positivity)
  exact (h.trans houter).trans_lt (final_union_bound_numeric hn)

theorem all_signings_exceed_iff_no_bad {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) (R : ReplacementBits C) :
    AllSigningsExceed (replaceColumns H C R) ((1+delta)*Real.sqrt n) ↔
      ¬ ∃ b : Fin n → Bool, replacementBadEvent H C R b := by
  constructor
  · intro h ⟨b,hb⟩
    exact not_lt_of_ge hb (h (fun j => bitSign (b j)) (fun j => bitSign_isSign _))
  · intro h x hx
    obtain ⟨b,rfl⟩ := (signings_iff_boolean x).mp hx
    by_contra hb
    exact h ⟨b,le_of_not_gt hb⟩

theorem successFraction_eq_one_sub_failure {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Finset (Fin n)) :
    successFraction H C = 1-uniformProb (fun R : ReplacementBits C =>
      ∃ b : Fin n → Bool, replacementBadEvent H C R b) := by
  change uniformProb (fun R : ReplacementBits C =>
    AllSigningsExceed (replaceColumns H C R) ((1+delta)*Real.sqrt n)) = _
  simp_rw [all_signings_exceed_iff_no_bad]
  exact uniformProb_compl _

/-- Theorem 1.1, with the exact random replacement model and probability. -/
theorem lowerBoundClaim_proof : LowerBoundClaim := by
  intro n hp hn H hH C hC
  rw [successFraction_eq_one_sub_failure]
  have h := replacement_failure_probability hp hn H hH C hC
  linarith

end Stoc393

end
/- END original module: Stoc393.LowerBound -/

/- BEGIN original module: Stoc393.SylvesterHadamard -/
section

/-! Existence of Hadamard matrices at all powers of two by Sylvester's construction. -/
open scoped Kronecker
set_option autoImplicit false
namespace Stoc393

def sylvesterTwo : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]

theorem sylvesterTwo_isHadamard : Matrix.IsHadamard sylvesterTwo := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sylvesterTwo,Unitary.mem_iff_eq_one_or_eq_neg_one]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvesterTwo,Matrix.mul_apply,Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvesterTwo,Matrix.mul_apply,Fin.sum_univ_two]

theorem exists_mathlib_hadamard_two_pow (m : ℕ) :
    ∃ H : Matrix (Fin (2^m)) (Fin (2^m)) ℝ, Matrix.IsHadamard H := by
  induction m with
  | zero =>
    refine ⟨(1 : Matrix (Fin (2^0)) (Fin (2^0)) ℝ),?_⟩
    constructor
    · intro i j
      have hij : i = j := by
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        norm_num at hi hj
        omega
      subst j
      simp
    · simp
    · simp
  | succ m ih =>
    obtain ⟨H,hH⟩ := ih
    let e : (Fin (2^m) × Fin 2) ≃ Fin (2^(m+1)) :=
      finProdFinEquiv.trans (finCongr (by rw [pow_succ]))
    exact ⟨Matrix.reindex e e (H ⊗ₖ sylvesterTwo),
      (hH.kronecker sylvesterTwo_isHadamard).reindex e e⟩

theorem custom_isHadamard_of_mathlib {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : Matrix.IsHadamard H) : IsHadamard H := by
  refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j),?_⟩
  intro j k
  have h := congrFun (congrFun hH.conjTranspose_mul j) k
  simpa [Matrix.mul_apply,Matrix.one_apply,Matrix.smul_apply] using h

theorem exists_hadamard_two_pow (m : ℕ) :
    ∃ H : Matrix (Fin (2^m)) (Fin (2^m)) ℝ, IsHadamard H := by
  obtain ⟨H,hH⟩ := exists_mathlib_hadamard_two_pow m
  exact ⟨H,custom_isHadamard_of_mathlib H hH⟩

end Stoc393

end
/- END original module: Stoc393.SylvesterHadamard -/

/- BEGIN original module: Stoc393.LowerCorollaries -/
section

/-! Existence at every sufficiently large power of two and the stated limsup corollary. -/
open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

theorem allSigningsExceed_iff_discrepancy_lt {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (D : ℝ) :
    AllSigningsExceed A D ↔ D < discrepancy A := by
  rw [← not_le,discrepancy_le_iff]
  constructor
  · intro h ⟨x,hx,hsmall⟩
    exact not_lt_of_ge hsmall (h x hx)
  · intro h x hx
    by_contra hsmall
    exact h ⟨x,hx,le_of_not_gt hsmall⟩

theorem exists_signed_matrix_lower_bound {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧ AllSigningsExceed A ((1+delta)*Real.sqrt n) := by
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨H,hH⟩ : ∃ H : Matrix (Fin n) (Fin n) ℝ, IsHadamard H := by
    obtain ⟨m,rfl⟩ := hp
    exact exists_hadamard_two_pow m
  have hle : noiseCount n ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ,Fintype.card_fin,noiseCount] using Nat.div_le_self n (2^22)
  obtain ⟨C,_,hC⟩ := Finset.exists_subset_card_eq hle
  have hCeq : (C.card:ℝ) = delta*n := by rw [hC]; exact (noiseCount_properties hp hn).1
  have hsuccess := lowerBoundClaim_proof n hp hn H hH C hCeq
  have htail : (2:ℝ)^(-(n:ℝ)/20000) < 1 := by
    rw [Real.rpow_def_of_pos (by norm_num),Real.exp_lt_one_iff]
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    exact mul_neg_of_pos_of_neg hlog (by linarith)
  have hpositive : 0 < uniformProb (fun R : ReplacementBits C =>
      AllSigningsExceed (replaceColumns H C R) ((1+delta)*Real.sqrt n)) := by
    change 0 < successFraction H C
    linarith
  obtain ⟨R,hR⟩ := (uniformProb_pos_iff _).mp hpositive
  exact ⟨replaceColumns H C R,replaced_entries_are_signs hH C R,hR⟩

theorem signed_entries_bounded {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : ∀ i j, A i j = 1 ∨ A i j = -1) : EntryBounded A := by
  intro i j
  rcases hA i j with h|h <;> norm_num [h]

theorem signExtremalDiscrepancy_set_bddAbove {n : ℕ} (hn : 0 < n) :
    BddAbove {r : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧ r = discrepancy A/Real.sqrt n} := by
  refine ⟨Real.sqrt (3*Real.arsinh 10)+4/Real.sqrt n,?_⟩
  rintro r ⟨A,hA,rfl⟩
  exact square_matrix_normalized_bound hn A (signed_entries_bounded hA)

theorem signExtremalDiscrepancy_upper_bound {n : ℕ} (hn : 0 < n) :
    signExtremalDiscrepancy n ≤ Real.sqrt (3*Real.arsinh 10)+4/Real.sqrt n := by
  apply csSup_le
  · refine ⟨discrepancy (fun _ _ => (1:ℝ))/Real.sqrt n,fun _ _ => 1,?_,rfl⟩
    intro i j
    exact Or.inl rfl
  · rintro r ⟨A,hA,rfl⟩
    exact square_matrix_normalized_bound hn A (signed_entries_bounded hA)

theorem signExtremalDiscrepancy_lower_bound {n : ℕ} (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n) :
    1+delta < signExtremalDiscrepancy n := by
  have hnpos : 0 < n := by omega
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  obtain ⟨A,hA,hdisc⟩ := exists_signed_matrix_lower_bound hp hn
  have hd := (allSigningsExceed_iff_discrepancy_lt A _).mp hdisc
  have hnorm : 1+delta < discrepancy A/Real.sqrt n := (lt_div_iff₀ hs).mpr hd
  exact hnorm.trans_le (le_csSup (signExtremalDiscrepancy_set_bddAbove hnpos) ⟨A,hA,rfl⟩)

theorem signExtremalDiscrepancy_limsup_lower_bound :
    1+delta ≤ Filter.limsup signExtremalDiscrepancy Filter.atTop := by
  have hfreq : ∃ᶠ n in Filter.atTop, 1+delta ≤ signExtremalDiscrepancy n := by
    rw [Filter.frequently_atTop]
    intro N
    let m := max 50 N
    have hm50 : 50 ≤ m := Nat.le_max_left _ _
    have hmN : N ≤ m := Nat.le_max_right _ _
    refine ⟨2^m,hmN.trans (show m < 2^m from Nat.lt_two_pow_self).le,?_⟩
    exact (signExtremalDiscrepancy_lower_bound ⟨m,rfl⟩
      ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hm50)).le
  have hbounded : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop signExtremalDiscrepancy := by
    apply Filter.isBoundedUnder_of_eventually_le (a := Real.sqrt (3*Real.arsinh 10)+4)
    rw [Filter.eventually_atTop]
    refine ⟨1,?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hs : (1:ℝ) ≤ Real.sqrt n := by
      apply Real.le_sqrt_of_sq_le
      norm_num
      exact_mod_cast hn
    have hdiv : (4:ℝ)/Real.sqrt n ≤ 4 := by
      apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (n:ℝ))).mpr
      linarith
    exact (signExtremalDiscrepancy_upper_bound hnpos).trans (by linarith)
  exact Filter.le_limsup_of_frequently_le hfreq hbounded

/-- The numerical limsup conclusion stated after Theorem 1.1. -/
theorem bandeira_conjecture :
    (5000001:ℝ)/5000000 < Filter.limsup signExtremalDiscrepancy Filter.atTop := by
  have hδ : (5000001:ℝ)/5000000 < 1+delta := by rw [delta_value]; norm_num
  exact hδ.trans_le signExtremalDiscrepancy_limsup_lower_bound

/-- The existence bound stated in the abstract, with its exact decimal threshold. -/
theorem exists_signed_matrix_decimal_lower_bound {n : ℕ}
    (hp : ∃ m : ℕ, n = 2^m) (hn : 2^50 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧
      AllSigningsExceed A (((5000001:ℝ)/5000000)*Real.sqrt n) := by
  obtain ⟨A,hA,hbound⟩ := exists_signed_matrix_lower_bound hp hn
  refine ⟨A,hA,?_⟩
  intro x hx
  have hδ : (5000001:ℝ)/5000000 ≤ 1+delta := by rw [delta_value]; norm_num
  exact (mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg _)).trans_lt (hbound x hx)

theorem complete_main_claims : CompleteMainClaims := ⟨upperBoundClaim_proof,lowerBoundClaim_proof⟩

end Stoc393

end
/- END original module: Stoc393.LowerCorollaries -/

/-! ## Main theorems -/

namespace Stoc393

/-- Theorem 1.1: the random-Hadamard lower bound, with the exact model and constants. -/
theorem theorem_1_1 : LowerBoundClaim := lowerBoundClaim_proof

/-- Theorem 1.2: Spencer's upper bound, including degenerate dimensions. -/
theorem theorem_1_2 : UpperBoundClaim := upperBoundClaim_proof

end Stoc393

-- Completion checks: neither main theorem should depend on sorryAx.
#print axioms Stoc393.theorem_1_1
#print axioms Stoc393.theorem_1_2
