-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/863d0af0-a734-5358-9c9e-d1cf7825c547

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice
import Theorems.Thm_AutomorphicForm_GL2Real_ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin
import Theorems.Thm_AutomorphicForm_GL2Real_contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU
import Theorems.Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
import Theorems.Thm_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq
import Theorems.Thm_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq
import Theorems.Thm_AutomorphicForm_GL2Real_discreteSeriesPairing_entrySlice_eq_zero_of_weight
import Theorems.Thm_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Real

noncomputable section

namespace BiFiniteSynthesis

private def unitFamily (u : (Fin 2 → Fin 2 → ℝ) → ℂ) : (Fin 2 → Fin 2 → ℝ) × Unit → ℂ := fun q => u q.1

private theorem contDiff_unitFamily {u : (Fin 2 → Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (unitFamily u) :=
  hu.comp contDiff_fst

private theorem support_unitFamily (u : (Fin 2 → Fin 2 → ℝ) → ℂ) :
    Function.support (unitFamily u) = Function.support u ×ˢ (Set.univ : Set Unit) := by
  ext ⟨M, p⟩
  simp [unitFamily]

private theorem tsupport_unitFamily_eq (u : (Fin 2 → Fin 2 → ℝ) → ℂ) :
    tsupport (unitFamily u) = tsupport u ×ˢ (Set.univ : Set Unit) := by
  rw [tsupport, tsupport, support_unitFamily, closure_prod_eq, closure_univ]

private theorem hasCompactSupport_unitFamily {u : (Fin 2 → Fin 2 → ℝ) → ℂ} (huc : HasCompactSupport u) :
    HasCompactSupport (unitFamily u) := by
  rw [HasCompactSupport, tsupport_unitFamily_eq]
  exact huc.prod isCompact_univ

private theorem tsupport_unitFamily {u : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (huinv : tsupport u ⊆ {M | IsUnit (Matrix.det (Matrix.of M))}) :
    tsupport (unitFamily u) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  intro q hq
  rw [tsupport_unitFamily_eq] at hq
  exact huinv hq.1

private theorem continuous_entrySlice {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (p : P) : Continuous (entrySlice Φ p) :=
  hΦ.comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)).prodMk continuous_const)

private def conjEntries (θ a₁ a₂ u : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![Real.cos θ ^ 2 * a₁ + Real.cos θ * Real.sin θ * u + Real.sin θ ^ 2 * a₂,
      -(Real.cos θ * Real.sin θ * a₁) + Real.cos θ ^ 2 * u + Real.cos θ * Real.sin θ * a₂],
    ![-(Real.cos θ * Real.sin θ * a₁) + Real.cos θ * Real.sin θ * a₂ - Real.sin θ ^ 2 * u,
      Real.sin θ ^ 2 * a₁ - Real.cos θ * Real.sin θ * u + Real.cos θ ^ 2 * a₂]]

private lemma rotationMatrix_mul_upper_mul_inv (θ a₁ a₂ u : ℝ) :
    (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) * !![a₁, u; 0, a₂] *
        !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] =
      Matrix.of (conjEntries θ a₁ a₂ u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjEntries, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma rotationMatrix_inv (θ : ℝ) :
    (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.cos_sq_add_sin_sq θ]

private lemma det_of_conjEntries (θ a₁ a₂ u : ℝ) : Matrix.det (Matrix.of (conjEntries θ a₁ a₂ u)) = a₁ * a₂ := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, conjEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (a₁ * a₂ * (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1)) * Real.cos_sq_add_sin_sq θ

private lemma sum_sq_conjEntries (θ a₁ a₂ u : ℝ) :
    conjEntries θ a₁ a₂ u 0 0 ^ 2 + conjEntries θ a₁ a₂ u 0 1 ^ 2 + conjEntries θ a₁ a₂ u 1 0 ^ 2 +
        conjEntries θ a₁ a₂ u 1 1 ^ 2 =
      a₁ ^ 2 + a₂ ^ 2 + u ^ 2 := by
  simp only [conjEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((a₁ ^ 2 + a₂ ^ 2 + u ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1)) *
    Real.cos_sq_add_sin_sq θ

private lemma abs_le_of_norm_conjEntries_le {θ a₁ a₂ u R : ℝ} (h : ‖conjEntries θ a₁ a₂ u‖ ≤ R) :
    |a₁| ≤ 2 * R ∧ |a₂| ≤ 2 * R ∧ |u| ≤ 2 * R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans h
  have hsq : ∀ i j : Fin 2, conjEntries θ a₁ a₂ u i j ^ 2 ≤ R ^ 2 := by
    intro i j
    have h1 : ‖conjEntries θ a₁ a₂ u i j‖ ≤ R :=
      (norm_le_pi_norm (conjEntries θ a₁ a₂ u i) j).trans ((norm_le_pi_norm (conjEntries θ a₁ a₂ u) i).trans h)
    rw [Real.norm_eq_abs] at h1
    nlinarith [abs_nonneg (conjEntries θ a₁ a₂ u i j), sq_abs (conjEntries θ a₁ a₂ u i j)]
  have hsum := sum_sq_conjEntries θ a₁ a₂ u
  have h00 := hsq 0 0
  have h01 := hsq 0 1
  have h10 := hsq 1 0
  have h11 := hsq 1 1
  refine ⟨abs_le_of_sq_le_sq ?_ (by linarith), abs_le_of_sq_le_sq ?_ (by linarith),
    abs_le_of_sq_le_sq ?_ (by linarith)⟩ <;> nlinarith [sq_nonneg a₁, sq_nonneg a₂, sq_nonneg u]

private lemma conjEntries_eq_of_symm_coe (θ a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    Matrix.of.symm ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = conjEntries θ a₁ a₂ u := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  change Matrix.of.symm ((!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) *
    !![a₁, u; 0, a₂] * (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹) = _
  rw [rotationMatrix_inv, rotationMatrix_mul_upper_mul_inv]
  exact Matrix.of.symm_apply_apply _

private lemma continuous_conjEntries_right (θ a₁ a₂ : ℝ) : Continuous fun u : ℝ => conjEntries θ a₁ a₂ u := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [conjEntries] <;> simp <;> fun_prop

private lemma continuous_conjEntries_left (a₁ a₂ u : ℝ) : Continuous fun θ : ℝ => conjEntries θ a₁ a₂ u := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [conjEntries] <;> simp <;> fun_prop

private lemma _root_.BiFiniteSynthesis.exists_norm_le {P : Type} [TopologicalSpace P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) : ∃ C : ℝ, ∀ q, ‖Φ q‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΦc.isCompact.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max C 0, fun q => ?_⟩
  by_cases hq : q ∈ tsupport Φ
  · exact (hC q hq).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hq, norm_zero]
    exact le_max_right _ _

p2m_export "BiFiniteSynthesis" "exists_norm_le"

private lemma line_eq_zero {P : Type} [TopologicalSpace P] {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {R : ℝ}
    (hR : ∀ x ∈ Prod.fst '' tsupport Φ, ‖x‖ ≤ R) (p : P) (θ a₁ a₂ u : ℝ)
    (hu : u ∉ Set.Icc (-(2 * R)) (2 * R)) : Φ (conjEntries θ a₁ a₂ u, p) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hnorm : ‖conjEntries θ a₁ a₂ u‖ ≤ R := hR _ ⟨_, hmem, rfl⟩
  obtain ⟨-, -, h⟩ := abs_le_of_norm_conjEntries_le hnorm
  exact hu (Set.mem_Icc.2 (abs_le.1 h))

private lemma integrable_line {P : Type} [TopologicalSpace P] {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} (hΦ : Continuous Φ)
    {R : ℝ} (hR : ∀ x ∈ Prod.fst '' tsupport Φ, ‖x‖ ≤ R) (p : P) (θ a₁ a₂ : ℝ) :
    Integrable fun u : ℝ => Φ (conjEntries θ a₁ a₂ u, p) := by
  have hcont : Continuous fun u : ℝ => Φ (conjEntries θ a₁ a₂ u, p) :=
    hΦ.comp ((continuous_conjEntries_right θ a₁ a₂).prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun u hu => line_eq_zero hR p θ a₁ a₂ u hu)

private lemma continuous_lineIntegral {P : Type} [TopologicalSpace P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : P) (a₁ a₂ : ℝ) :
    Continuous fun θ : ℝ => ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) := by
  obtain ⟨R, hR⟩ := (hΦc.isCompact.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := exists_norm_le Φ hΦ hΦc
  refine continuous_of_dominated (bound := (Set.Icc (-(2 * R)) (2 * R)).indicator fun _ => C) ?_ ?_ ?_ ?_
  · intro θ
    exact (hΦ.comp ((continuous_conjEntries_right θ a₁ a₂).prodMk continuous_const)).aestronglyMeasurable
  · intro θ
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Set.indicator_apply]
    split_ifs with hu
    · exact hC _
    · exact (by rw [line_eq_zero hR p θ a₁ a₂ u hu, norm_zero] : ‖Φ (conjEntries θ a₁ a₂ u, p)‖ = 0).le
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · refine Filter.Eventually.of_forall fun u => ?_
    exact hΦ.comp ((continuous_conjEntries_left a₁ a₂ u).prodMk continuous_const)

private lemma continuous_sum {P : Type} [TopologicalSpace P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ∀ i ∈ s, Continuous (Φ i)) : Continuous (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact continuous_const
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hΦ a (Finset.mem_insert_self a s)).add (ih fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

private lemma hasCompactSupport_add {P : Type} [TopologicalSpace P] [T2Space P] {Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ}
    (hΦc : HasCompactSupport Φ) (hΨc : HasCompactSupport Ψ) : HasCompactSupport (Φ + Ψ) := by
  refine HasCompactSupport.intro (hΦc.isCompact.union hΨc.isCompact) fun q hq => ?_
  rw [Set.mem_union, not_or] at hq
  rw [Pi.add_apply, image_eq_zero_of_notMem_tsupport hq.1, image_eq_zero_of_notMem_tsupport hq.2, add_zero]

private lemma hasCompactSupport_sum {P : Type} [TopologicalSpace P] [T2Space P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦc : ∀ i ∈ s, HasCompactSupport (Φ i)) :
    HasCompactSupport (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact HasCompactSupport.intro isCompact_empty fun q _ => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasCompactSupport_add (hΦc a (Finset.mem_insert_self a s))
      (ih fun i hi => hΦc i (Finset.mem_insert_of_mem hi))

private lemma splitTransform_entrySlice_zero {P : Type} (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (0 : (Fin 2 → Fin 2 → ℝ) × P → ℂ) p) a₁ a₂ = 0 := by
  unfold splitTransform
  split_ifs <;> simp [entrySlice]

private def unitOf (M : {M : Matrix (Fin 2) (Fin 2) ℝ // IsUnit M.det}) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 (isUnit_iff_ne_zero.1 M.2)

private lemma continuous_unitOf : Continuous unitOf := by
  have hinv : Continuous fun M : {M : Matrix (Fin 2) (Fin 2) ℝ // IsUnit M.det} => (M.1)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun M => ?_
    obtain ⟨v, hv⟩ := M.2
    have h := NormedRing.inverse_continuousAt v
    rw [hv] at h
    exact (continuousAt_matrix_inv M.1 h).comp continuous_subtype_val.continuousAt
  exact Units.continuous_iff.2 ⟨continuous_subtype_val, hinv.congr fun M => (Matrix.coe_units_inv (unitOf M)).symm⟩

private theorem hasCompactSupport_entrySlice {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦc : HasCompactSupport Φ) (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (p : P) :
    HasCompactSupport (entrySlice Φ p) := by

  have hK₁ : IsCompact ((fun q : (Fin 2 → Fin 2 → ℝ) × P => Matrix.of q.1) '' tsupport Φ) :=
    hΦc.isCompact.image continuous_fst
  have hunit : ∀ M ∈ (fun q : (Fin 2 → Fin 2 → ℝ) × P => Matrix.of q.1) '' tsupport Φ, IsUnit M.det := by
    rintro _ ⟨q, hq, rfl⟩
    have hm : q ∈ {q : (Fin 2 → Fin 2 → ℝ) × P | IsUnit (Matrix.det (Matrix.of q.1))} := hΦinv hq
    rw [Set.mem_setOf_eq] at hm
    exact hm

  have hK₂ : IsCompact {M : {M : Matrix (Fin 2) (Fin 2) ℝ // IsUnit M.det} |
      M.1 ∈ (fun q : (Fin 2 → Fin 2 → ℝ) × P => Matrix.of q.1) '' tsupport Φ} := by
    rw [Subtype.isCompact_iff]
    convert hK₁ using 1
    ext A
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact hM
    · intro hA
      exact ⟨⟨A, hunit A hA⟩, hA, rfl⟩
  refine HasCompactSupport.intro (hK₂.image continuous_unitOf) fun g hg => ?_
  by_contra hne
  have hmem : (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p) ∈ tsupport Φ := subset_tsupport _ hne
  have hgK : (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ (fun q : (Fin 2 → Fin 2 → ℝ) × P => Matrix.of q.1) '' tsupport Φ :=
    ⟨_, hmem, Matrix.of.apply_symm_apply _⟩
  exact hg ⟨⟨(g : Matrix (Fin 2) (Fin 2) ℝ), hunit _ hgK⟩, hgK, Units.ext rfl⟩

private theorem splitTransform_entrySlice_add {P : Type} [NormedAddCommGroup P] (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (Φ + Ψ) p) a₁ a₂ =
      splitTransform (entrySlice Φ p) a₁ a₂ + splitTransform (entrySlice Ψ p) a₁ a₂ := by
  unfold splitTransform
  by_cases h : a₁ * a₂ ≠ 0
  · simp only [dif_pos h]
    have hconj : ∀ θ u : ℝ, Matrix.of.symm ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = conjEntries θ a₁ a₂ u :=
      fun θ u => conjEntries_eq_of_symm_coe θ a₁ a₂ u h
    simp only [entrySlice, hconj, Pi.add_apply]
    obtain ⟨R, hR⟩ := (hΦc.isCompact.image continuous_fst).isBounded.exists_norm_le
    obtain ⟨R', hR'⟩ := (hΨc.isCompact.image continuous_fst).isBounded.exists_norm_le
    have hinner : ∀ θ : ℝ, ∫ u : ℝ, (Φ (conjEntries θ a₁ a₂ u, p) + Ψ (conjEntries θ a₁ a₂ u, p)) =
        (∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p)) + ∫ u : ℝ, Ψ (conjEntries θ a₁ a₂ u, p) :=
      fun θ => integral_add (integrable_line hΦ hR p θ a₁ a₂) (integrable_line hΨ hR' p θ a₁ a₂)
    have houter : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p)) + ∫ u : ℝ, Ψ (conjEntries θ a₁ a₂ u, p)) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p)) +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, Ψ (conjEntries θ a₁ a₂ u, p) :=
      intervalIntegral.integral_add ((continuous_lineIntegral Φ hΦ hΦc p a₁ a₂).intervalIntegrable _ _)
        ((continuous_lineIntegral Ψ hΨ hΨc p a₁ a₂).intervalIntegrable _ _)
    simp only [hinner]
    rw [houter, mul_add]
  · simp only [dif_neg h, add_zero]

private theorem splitTransform_entrySlice_smul
    {P : Type} [NormedAddCommGroup P] (c : ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (c • Φ) p) a₁ a₂ = c * splitTransform (entrySlice Φ p) a₁ a₂ := by
  unfold splitTransform
  by_cases h : a₁ * a₂ ≠ 0
  · simp only [dif_pos h]
    have hconj : ∀ θ u : ℝ, Matrix.of.symm ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = conjEntries θ a₁ a₂ u :=
      fun θ u => conjEntries_eq_of_symm_coe θ a₁ a₂ u h
    simp only [entrySlice, hconj, Pi.smul_apply, smul_eq_mul]
    have hinner : ∀ θ : ℝ, ∫ u : ℝ, c * Φ (conjEntries θ a₁ a₂ u, p) = c * ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) :=
      fun θ => integral_const_mul c _
    have houter : ∫ θ in (0 : ℝ)..(2 * Real.pi), c * ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) =
        c * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) :=
      intervalIntegral.integral_const_mul c _
    simp only [hinner]
    rw [houter]
    ring
  · simp only [dif_neg h, mul_zero]

private theorem splitTransform_entrySlice_sum {P : Type} [NormedAddCommGroup P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ∀ i ∈ s, Continuous (Φ i)) (hΦc : ∀ i ∈ s, HasCompactSupport (Φ i))
    (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (∑ i ∈ s, Φ i) p) a₁ a₂ = ∑ i ∈ s, splitTransform (entrySlice (Φ i) p) a₁ a₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact splitTransform_entrySlice_zero p a₁ a₂
  | @insert a s ha ih =>
    have hΦ' : ∀ i ∈ s, Continuous (Φ i) := fun i hi => hΦ i (Finset.mem_insert_of_mem hi)
    have hΦc' : ∀ i ∈ s, HasCompactSupport (Φ i) := fun i hi => hΦc i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      splitTransform_entrySlice_add (Φ a) (∑ i ∈ s, Φ i) (hΦ a (Finset.mem_insert_self a s))
        (hΦc a (Finset.mem_insert_self a s)) (continuous_sum s Φ hΦ') (hasCompactSupport_sum s Φ hΦc') p a₁ a₂,
      ih hΦ' hΦc']

private theorem splitTransform_entrySlice_detMul {P : Type} [NormedAddCommGroup P] (χ : ℝ → ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p) a₁ a₂ =
      χ (a₁ * a₂) * splitTransform (entrySlice Φ p) a₁ a₂ := by
  unfold splitTransform
  by_cases h : a₁ * a₂ ≠ 0
  · simp only [dif_pos h]
    have hconj : ∀ θ u : ℝ, Matrix.of.symm ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = conjEntries θ a₁ a₂ u :=
      fun θ u => conjEntries_eq_of_symm_coe θ a₁ a₂ u h
    simp only [entrySlice, hconj, det_of_conjEntries]
    have hinner : ∀ θ : ℝ, ∫ u : ℝ, χ (a₁ * a₂) * Φ (conjEntries θ a₁ a₂ u, p) =
        χ (a₁ * a₂) * ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) :=
      fun θ => integral_const_mul (χ (a₁ * a₂)) _
    have houter : ∫ θ in (0 : ℝ)..(2 * Real.pi), χ (a₁ * a₂) * ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) =
        χ (a₁ * a₂) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, Φ (conjEntries θ a₁ a₂ u, p) :=
      intervalIntegral.integral_const_mul (χ (a₁ * a₂)) _
    simp only [hinner]
    rw [houter]
    ring
  · simp only [dif_neg h, mul_zero]

private noncomputable def conjMat (r θ x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (Real.cos θ - x * Real.sin θ / y), r * Real.sin θ * (x ^ 2 + y ^ 2) / y;
    -(r * Real.sin θ / y), r * (Real.cos θ + x * Real.sin θ / y)]

private theorem conjugate_eq_conjMat (r θ x y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    ((upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = conjMat r θ x y := by
  have hg : ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] := by
    simp [upperHalfPlaneElt]
  have hγ : ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := by
    simp [ellipticElt]
  have h1 : ((upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) * ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  have h2 : conjMat r θ x y * ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hy0 : y ≠ 0 := hy.ne'
    rw [hg, hγ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring1
  exact (Units.isUnit (upperHalfPlaneElt x y hy)).mul_left_injective (h1.trans h2.symm)

private noncomputable def ellipticKernel {P : Type} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P)
    (r θ x y : ℝ) : ℂ :=
  if 0 < y then
    (Φ (Matrix.of.symm (conjMat r θ x y), p) + Φ (Matrix.of.symm (conjMat r (-θ) x y), p)) / ((y : ℂ) ^ 2)
  else 0

private theorem ellipticTransform_entrySlice_eq {P : Type} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ellipticTransform (entrySlice Φ p) r θ =
      (4 * Real.sin θ ^ 2 : ℂ) * ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, ellipticKernel Φ p r θ x y := by
  simp only [ellipticTransform, dif_pos hr]
  congr 1
  congr 1
  funext y
  congr 1
  funext x
  unfold ellipticKernel
  by_cases hy : 0 < y
  · rw [dif_pos hy, if_pos hy]
    simp only [entrySlice, conjugate_eq_conjMat r θ x y hr hy, conjugate_eq_conjMat r (-θ) x y hr hy]
  · rw [dif_neg hy, if_neg hy]

private theorem ellipticTransform_of_sin_eq_zero (f : GL (Fin 2) ℝ → ℂ) (r : ℝ) {θ : ℝ} (hs : Real.sin θ = 0) :
    ellipticTransform f r θ = 0 := by
  unfold ellipticTransform
  by_cases hr : 0 < r
  · rw [dif_pos hr]
    simp [hs]
  · rw [dif_neg hr]

private theorem ellipticTransform_entrySlice_zero {P : Type} (p : P) (r θ : ℝ) :
    ellipticTransform (entrySlice (0 : (Fin 2 → Fin 2 → ℝ) × P → ℂ) p) r θ = 0 := by
  by_cases hr : 0 < r
  · simp [ellipticTransform, hr, entrySlice]
  · simp [ellipticTransform, hr]

private theorem det_conjMat (r θ x y : ℝ) (hy : y ≠ 0) : Matrix.det (conjMat r θ x y) = r ^ 2 := by
  have h : Matrix.det (conjMat r θ x y) = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
    unfold conjMat
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  rw [h, Real.cos_sq_add_sin_sq, mul_one]

private theorem ellipticKernel_neg {P : Type} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r θ x y : ℝ) :
    ellipticKernel Φ p r (-θ) x y = ellipticKernel Φ p r θ x y := by
  unfold ellipticKernel
  rw [neg_neg]
  split_ifs with hy <;> simp only [add_comm]

private theorem ellipticKernel_add {P : Type} (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r θ x y : ℝ) :
    ellipticKernel (Φ + Ψ) p r θ x y = ellipticKernel Φ p r θ x y + ellipticKernel Ψ p r θ x y := by
  unfold ellipticKernel
  split_ifs with hy
  · simp only [Pi.add_apply]
    ring
  · rw [add_zero]

private theorem ellipticKernel_smul {P : Type} (c : ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r θ x y : ℝ) :
    ellipticKernel (c • Φ) p r θ x y = c * ellipticKernel Φ p r θ x y := by
  unfold ellipticKernel
  split_ifs with hy
  · simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [mul_zero]

private theorem ellipticKernel_detMul {P : Type} (χ : ℝ → ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P)
    (r θ x y : ℝ) :
    ellipticKernel (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p r θ x y =
      χ (r ^ 2) * ellipticKernel Φ p r θ x y := by
  unfold ellipticKernel
  split_ifs with hy
  · simp only [Equiv.apply_symm_apply, det_conjMat r θ x y hy.ne', det_conjMat r (-θ) x y hy.ne']
    ring
  · rw [mul_zero]

private theorem exists_entryBound {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (A : Fin 2 → Fin 2 → ℝ) (p : P), Φ (A, p) ≠ 0 → ∀ i j, |A i j| ≤ B := by
  obtain ⟨B₀, hB₀⟩ := isBounded_iff_forall_norm_le.mp (IsCompact.image hΦc continuous_fst).isBounded
  refine ⟨max B₀ 1, le_max_right _ _, fun A p hAp i j => ?_⟩
  have hmem : A ∈ Prod.fst '' tsupport Φ := ⟨(A, p), subset_tsupport Φ (Function.mem_support.mpr hAp), rfl⟩
  calc |A i j| = ‖A i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A i‖ := norm_le_pi_norm (A i) j
    _ ≤ ‖A‖ := norm_le_pi_norm A i
    _ ≤ B₀ := hB₀ A hmem
    _ ≤ max B₀ 1 := le_max_left _ _

private theorem exists_normBound {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖Φ z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc
  exact ⟨max M 0, le_max_right _ _, fun z => (hM z).trans (le_max_left _ _)⟩

private theorem entries_le_of_ne_zero {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    {B : ℝ} (hB : ∀ (A : Fin 2 → Fin 2 → ℝ) (p : P), Φ (A, p) ≠ 0 → ∀ i j, |A i j| ≤ B) (p : P)
    (r θ x y : ℝ) (hr : 0 < r) (hy : 0 < y) (h : Φ (Matrix.of.symm (conjMat r θ x y), p) ≠ 0) :
    r * |Real.sin θ| ≤ B * y ∧ r * |Real.sin θ| * (x ^ 2 + y ^ 2) ≤ B * y := by
  have h10 := hB _ p h 1 0
  have h01 := hB _ p h 0 1
  have e10 : Matrix.of.symm (conjMat r θ x y) 1 0 = -(r * Real.sin θ / y) := by simp [conjMat]
  have e01 : Matrix.of.symm (conjMat r θ x y) 0 1 = r * Real.sin θ * (x ^ 2 + y ^ 2) / y := by simp [conjMat]
  rw [e10, abs_neg, abs_div, abs_mul, abs_of_pos hr, abs_of_pos hy, div_le_iff₀ hy] at h10
  rw [e01, abs_div, abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hy,
    abs_of_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)), div_le_iff₀ hy] at h01
  exact ⟨h10, h01⟩

private theorem kernel_support {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    {B : ℝ} (hB : ∀ (A : Fin 2 → Fin 2 → ℝ) (p : P), Φ (A, p) ≠ 0 → ∀ i j, |A i j| ≤ B) (p : P)
    {r θ x y : ℝ} (hr : 0 < r) (h : ellipticKernel Φ p r θ x y ≠ 0) :
    0 < y ∧ r * |Real.sin θ| ≤ B * y ∧ r * |Real.sin θ| * (x ^ 2 + y ^ 2) ≤ B * y := by
  unfold ellipticKernel at h
  by_cases hy : 0 < y
  · rw [if_pos hy] at h
    refine ⟨hy, ?_⟩
    by_cases h1 : Φ (Matrix.of.symm (conjMat r θ x y), p) = 0
    · have h2 : Φ (Matrix.of.symm (conjMat r (-θ) x y), p) ≠ 0 := by
        intro h2
        apply h
        rw [h1, h2]
        simp
      have h3 := entries_le_of_ne_zero Φ hB p r (-θ) x y hr hy h2
      simpa only [Real.sin_neg, abs_neg] using h3
    · exact entries_le_of_ne_zero Φ hB p r θ x y hr hy h1
  · rw [if_neg hy] at h
    exact (h rfl).elim

private theorem kernel_norm_le {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M) (p : P) (r θ x y : ℝ) (hy : 0 < y) :
    ‖ellipticKernel Φ p r θ x y‖ ≤ 2 * M / y ^ 2 := by
  unfold ellipticKernel
  rw [if_pos hy, norm_div, norm_pow, Complex.norm_of_nonneg hy.le]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg y)
  calc ‖Φ (Matrix.of.symm (conjMat r θ x y), p) + Φ (Matrix.of.symm (conjMat r (-θ) x y), p)‖
      ≤ ‖Φ (Matrix.of.symm (conjMat r θ x y), p)‖ + ‖Φ (Matrix.of.symm (conjMat r (-θ) x y), p)‖ :=
        norm_add_le _ _
    _ ≤ M + M := add_le_add (hM _) (hM _)
    _ = 2 * M := by ring

private theorem kernel_support_box {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    {B : ℝ} (hB : ∀ (A : Fin 2 → Fin 2 → ℝ) (p : P), Φ (A, p) ≠ 0 → ∀ i j, |A i j| ≤ B) (hBpos : 0 < B)
    {m : ℝ} (hm : 0 < m) (p : P) {r θ x y : ℝ} (hr : 0 < r) (hrs : m ≤ r * Real.sin θ)
    (h : ellipticKernel Φ p r θ x y ≠ 0) : m / B ≤ y ∧ y ≤ B / m ∧ |x| ≤ B / m := by
  obtain ⟨hy, h1, h2⟩ := kernel_support Φ hB p hr h
  have hsin : 0 < Real.sin θ := (pos_iff_pos_of_mul_pos (lt_of_lt_of_le hm hrs)).mp hr
  rw [abs_of_pos hsin] at h1 h2
  have h3 : m * (x ^ 2 + y ^ 2) ≤ B * y :=
    (mul_le_mul_of_nonneg_right hrs (add_nonneg (sq_nonneg x) (sq_nonneg y))).trans h2
  have hu0 : 0 ≤ B / m := (div_pos hBpos hm).le
  have hyB : y ≤ B / m := by
    rw [le_div_iff₀ hm]
    have h5 : y * m * y ≤ B * y := by nlinarith [mul_nonneg hm.le (sq_nonneg x)]
    exact le_of_mul_le_mul_right h5 hy
  refine ⟨?_, hyB, ?_⟩
  · rw [div_le_iff₀ hBpos]
    nlinarith
  · have hx1 : x ^ 2 ≤ B / m * y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [mul_nonneg hm.le (sq_nonneg y)]
    have hx2 : x ^ 2 ≤ (B / m) ^ 2 :=
      calc x ^ 2 ≤ B / m * y := hx1
        _ ≤ B / m * (B / m) := mul_le_mul_of_nonneg_left hyB hu0
        _ = (B / m) ^ 2 := (sq _).symm
    exact (Real.abs_le_sqrt hx2).trans_eq (Real.sqrt_sq hu0)

private theorem kernel_measurable {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (p : P) (r θ : ℝ) :
    Measurable (Function.uncurry fun y x : ℝ => ellipticKernel Φ p r θ x y) := by
  have hmat : ∀ θ' : ℝ, Measurable fun z : ℝ × ℝ => Matrix.of.symm (conjMat r θ' z.2 z.1) := by
    intro θ'
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [conjMat] <;> fun_prop
  have hΦp : Measurable fun A : Fin 2 → Fin 2 → ℝ => Φ (A, p) :=
    (hΦ.comp (Continuous.prodMk_left p)).measurable
  show Measurable fun z : ℝ × ℝ => ellipticKernel Φ p r θ z.2 z.1
  unfold ellipticKernel
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  refine Measurable.div (Measurable.add (hΦp.comp (hmat θ)) (hΦp.comp (hmat (-θ)))) ?_
  exact (Complex.measurable_ofReal.comp measurable_fst).pow_const 2

private theorem kernel_box {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    {B : ℝ} (hB : ∀ (A : Fin 2 → Fin 2 → ℝ) (p : P), Φ (A, p) ≠ 0 → ∀ i j, |A i j| ≤ B) (hBpos : 0 < B) (p : P)
    {r θ : ℝ} (hr : 0 < r) (hθ : Real.sin θ ≠ 0) {x y : ℝ} (h : ellipticKernel Φ p r θ x y ≠ 0) :
    r * |Real.sin θ| / B ≤ y ∧ y ≤ B / (r * |Real.sin θ|) ∧ |x| ≤ B / (r * |Real.sin θ|) := by
  have hm : 0 < r * |Real.sin θ| := mul_pos hr (abs_pos.2 hθ)
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have h' : ellipticKernel Φ p r (-θ) x y ≠ 0 := by rwa [ellipticKernel_neg]
    have hrs : r * |Real.sin θ| ≤ r * Real.sin (-θ) := le_of_eq (by rw [Real.sin_neg, abs_of_neg hneg])
    exact kernel_support_box Φ hB hBpos hm p hr hrs h'
  · have hrs : r * |Real.sin θ| ≤ r * Real.sin θ := le_of_eq (by rw [abs_of_pos hpos])
    exact kernel_support_box Φ hB hBpos hm p hr hrs h

private theorem integrable_kernel_prod {P : Type} [NormedAddCommGroup P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : P) {r θ : ℝ} (hr : 0 < r) (hθ : Real.sin θ ≠ 0) :
    Integrable (fun z : ℝ × ℝ => ellipticKernel Φ p r θ z.2 z.1)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨B, hB1, hB⟩ := exists_entryBound Φ hΦc
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  obtain ⟨M, hM0, hM⟩ := exists_normBound Φ hΦ hΦc
  have hm : 0 < r * |Real.sin θ| := mul_pos hr (abs_pos.2 hθ)
  have ha : 0 < r * |Real.sin θ| / B := div_pos hm hBpos
  have hC : ∀ z : ℝ × ℝ, ‖ellipticKernel Φ p r θ z.2 z.1‖ ≤
      (Set.Icc (r * |Real.sin θ| / B) (B / (r * |Real.sin θ|)) ×ˢ
        Set.Icc (-(B / (r * |Real.sin θ|))) (B / (r * |Real.sin θ|))).indicator
          (fun _ => 2 * M / (r * |Real.sin θ| / B) ^ 2) z := by
    intro z
    rw [Set.indicator_apply]
    split_ifs with hz
    · have hay : r * |Real.sin θ| / B ≤ z.1 := (Set.mem_Icc.1 (Set.mem_prod.1 hz).1).1
      have hy : 0 < z.1 := ha.trans_le hay
      calc ‖ellipticKernel Φ p r θ z.2 z.1‖ ≤ 2 * M / z.1 ^ 2 := kernel_norm_le Φ hM p r θ z.2 z.1 hy
        _ ≤ 2 * M / (r * |Real.sin θ| / B) ^ 2 := by gcongr
    · by_contra hne
      have hk : ellipticKernel Φ p r θ z.2 z.1 ≠ 0 := fun h0 => hne (le_of_eq (by rw [h0, norm_zero]))
      obtain ⟨h1, h2, h3⟩ := kernel_box Φ hB hBpos p hr hθ hk
      exact hz (Set.mem_prod.2 ⟨Set.mem_Icc.2 ⟨h1, h2⟩, Set.mem_Icc.2 (abs_le.1 h3)⟩)
  have hbox : (volume.restrict (Set.Ioi (0 : ℝ))).prod volume
      (Set.Icc (r * |Real.sin θ| / B) (B / (r * |Real.sin θ|)) ×ˢ
        Set.Icc (-(B / (r * |Real.sin θ|))) (B / (r * |Real.sin θ|))) ≠ ⊤ := by
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Icc]
    exact (ENNReal.mul_lt_top ((measure_mono Set.inter_subset_left).trans_lt measure_Icc_lt_top)
      measure_Icc_lt_top).ne
  have hbound : Integrable ((Set.Icc (r * |Real.sin θ| / B) (B / (r * |Real.sin θ|)) ×ˢ
      Set.Icc (-(B / (r * |Real.sin θ|))) (B / (r * |Real.sin θ|))).indicator
        fun _ : ℝ × ℝ => 2 * M / (r * |Real.sin θ| / B) ^ 2) ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    (integrableOn_const hbox).integrable_indicator (measurableSet_Icc.prod measurableSet_Icc)
  exact hbound.mono' (kernel_measurable Φ hΦ p r θ).aestronglyMeasurable (ae_of_all _ hC)

private theorem ellipticTransform_entrySlice_add {P : Type} [NormedAddCommGroup P] (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (p : P) (r θ : ℝ) :
    ellipticTransform (entrySlice (Φ + Ψ) p) r θ =
      ellipticTransform (entrySlice Φ p) r θ + ellipticTransform (entrySlice Ψ p) r θ := by
  by_cases hs : Real.sin θ = 0
  · rw [ellipticTransform_of_sin_eq_zero _ _ hs, ellipticTransform_of_sin_eq_zero _ _ hs,
      ellipticTransform_of_sin_eq_zero _ _ hs, add_zero]
  by_cases hr : 0 < r
  · rw [ellipticTransform_entrySlice_eq _ p hr θ, ellipticTransform_entrySlice_eq Φ p hr θ,
      ellipticTransform_entrySlice_eq Ψ p hr θ, ← mul_add]
    congr 1
    have hΦi := integrable_kernel_prod Φ hΦ hΦc p hr hs
    have hΨi := integrable_kernel_prod Ψ hΨ hΨc p hr hs
    have hker : ∀ x y : ℝ, ellipticKernel (Φ + Ψ) p r θ x y =
        ellipticKernel Φ p r θ x y + ellipticKernel Ψ p r θ x y :=
      ellipticKernel_add Φ Ψ p r θ
    simp only [hker]
    rw [← integral_add hΦi.integral_prod_left hΨi.integral_prod_left]
    refine integral_congr_ae ?_
    filter_upwards [hΦi.prod_right_ae, hΨi.prod_right_ae] with y hy₁ hy₂
    exact integral_add hy₁ hy₂
  · simp only [ellipticTransform, dif_neg hr, add_zero]

private theorem ellipticTransform_entrySlice_smul {P : Type} [NormedAddCommGroup P] (c : ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r θ : ℝ) :
    ellipticTransform (entrySlice (c • Φ) p) r θ = c * ellipticTransform (entrySlice Φ p) r θ := by
  by_cases hr : 0 < r
  · rw [ellipticTransform_entrySlice_eq _ p hr θ, ellipticTransform_entrySlice_eq Φ p hr θ]
    have hker : ∀ x y : ℝ, ellipticKernel (c • Φ) p r θ x y = c * ellipticKernel Φ p r θ x y :=
      ellipticKernel_smul c Φ p r θ
    simp only [hker]
    have hinner : ∀ y : ℝ, ∫ x : ℝ, c * ellipticKernel Φ p r θ x y = c * ∫ x : ℝ, ellipticKernel Φ p r θ x y :=
      fun y => integral_const_mul c _
    have houter : ∫ y in Set.Ioi (0 : ℝ), c * ∫ x : ℝ, ellipticKernel Φ p r θ x y =
        c * ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, ellipticKernel Φ p r θ x y :=
      integral_const_mul c _
    simp only [hinner]
    rw [houter]
    ring
  · simp only [ellipticTransform, dif_neg hr, mul_zero]

private theorem ellipticTransform_entrySlice_sum {P : Type} [NormedAddCommGroup P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ∀ i ∈ s, Continuous (Φ i)) (hΦc : ∀ i ∈ s, HasCompactSupport (Φ i))
    (p : P) (r θ : ℝ) :
    ellipticTransform (entrySlice (∑ i ∈ s, Φ i) p) r θ = ∑ i ∈ s, ellipticTransform (entrySlice (Φ i) p) r θ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ellipticTransform_entrySlice_zero p r θ
  | @insert a s ha ih =>
    have hΦ' : ∀ i ∈ s, Continuous (Φ i) := fun i hi => hΦ i (Finset.mem_insert_of_mem hi)
    have hΦc' : ∀ i ∈ s, HasCompactSupport (Φ i) := fun i hi => hΦc i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ellipticTransform_entrySlice_add (Φ a) (∑ i ∈ s, Φ i) (hΦ a (Finset.mem_insert_self a s))
        (hΦc a (Finset.mem_insert_self a s)) (continuous_sum s Φ hΦ') (hasCompactSupport_sum s Φ hΦc')
        p r θ,
      ih hΦ' hΦc']

private theorem ellipticTransform_entrySlice_detMul {P : Type} [NormedAddCommGroup P] (χ : ℝ → ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r θ : ℝ) :
    ellipticTransform (entrySlice (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p) r θ =
      χ (r ^ 2) * ellipticTransform (entrySlice Φ p) r θ := by
  by_cases hr : 0 < r
  · rw [ellipticTransform_entrySlice_eq _ p hr θ, ellipticTransform_entrySlice_eq Φ p hr θ]
    have hker : ∀ x y : ℝ, ellipticKernel (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p r θ x y =
        χ (r ^ 2) * ellipticKernel Φ p r θ x y :=
      ellipticKernel_detMul χ Φ p r θ
    simp only [hker]
    have hinner : ∀ y : ℝ, ∫ x : ℝ, χ (r ^ 2) * ellipticKernel Φ p r θ x y =
        χ (r ^ 2) * ∫ x : ℝ, ellipticKernel Φ p r θ x y :=
      fun y => integral_const_mul (χ (r ^ 2)) _
    have houter : ∫ y in Set.Ioi (0 : ℝ), χ (r ^ 2) * ∫ x : ℝ, ellipticKernel Φ p r θ x y =
        χ (r ^ 2) * ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, ellipticKernel Φ p r θ x y :=
      integral_const_mul (χ (r ^ 2)) _
    simp only [hinner]
    rw [houter]
    ring
  · simp only [ellipticTransform, dif_neg hr, mul_zero]

private def rotM (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, s; -s, c]

private theorem exists_rotM_eq (k : rowIsometrySubgroup₀ ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM c s := by
  obtain ⟨h10, h11, hcs⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  refine ⟨_, _, hcs, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, h10, h11]

private theorem det_rotM (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Matrix.det (rotM c s) = 1 := by
  simp only [rotM, Matrix.det_fin_two_of]; linear_combination h

private theorem archWeightCharℝ_natCast_apply (n : ℕ) (k : rowIsometrySubgroup₀ ℝ) {c s : ℝ}
    (e : ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM c s) :
    ((archWeightCharℝ (n : ℤ) k : ℂˣ) : ℂ) = (⟨c, s⟩ : ℂ) ^ n := by
  have h1 : ((archWeightOneℝ k : ℂˣ) : ℂ) = ⟨c, s⟩ := by
    show firstRowℂ (k : GL (Fin 2) ℝ) = _
    rw [show firstRowℂ (k : GL (Fin 2) ℝ) =
        ⟨((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0, ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩
        from rfl, e]
    simp [rotM]
  rw [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, h1, zpow_natCast]

private def wt (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨M 0 0 + M 1 1, M 0 1 - M 1 0⟩

private def nsq (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

private theorem wt_rotM_mul (c s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    wt (rotM c s * M) = (⟨c, s⟩ : ℂ) * wt M := by
  apply Complex.ext <;> simp [wt, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem wt_mul_rotM (c s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    wt (M * rotM c s) = (⟨c, s⟩ : ℂ) * wt M := by
  apply Complex.ext <;> simp [wt, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem nsq_rotM_mul (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    nsq (rotM c s * M) = nsq M := by
  simp only [nsq, rotM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) * h

private theorem nsq_mul_rotM (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    nsq (M * rotM c s) = nsq M := by
  simp only [nsq, rotM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) * h

private def core (φ : ℝ → ℝ) (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (φ ((nsq M - 2 * Matrix.det M) / Matrix.det M) : ℂ) * wt M ^ k

private def member (ψ φ : ℝ → ℝ) (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (ψ (Matrix.det M) : ℂ) * core φ k M

private theorem core_rotM_mul (φ : ℝ → ℝ) (k : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : core φ k (rotM c s * M) = (⟨c, s⟩ : ℂ) ^ k * core φ k M := by
  rw [core, core, Matrix.det_mul, det_rotM c s h, one_mul, nsq_rotM_mul c s h, wt_rotM_mul, mul_pow]
  ring

private theorem core_mul_rotM (φ : ℝ → ℝ) (k : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : core φ k (M * rotM c s) = (⟨c, s⟩ : ℂ) ^ k * core φ k M := by
  rw [core, core, Matrix.det_mul, det_rotM c s h, mul_one, nsq_mul_rotM c s h, wt_mul_rotM, mul_pow]
  ring

private theorem member_rotM_mul (ψ φ : ℝ → ℝ) (k : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : member ψ φ k (rotM c s * M) = (⟨c, s⟩ : ℂ) ^ k * member ψ φ k M := by
  rw [member, member, core_rotM_mul φ k c s h, Matrix.det_mul, det_rotM c s h, one_mul]
  ring

private theorem member_mul_rotM (ψ φ : ℝ → ℝ) (k : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : member ψ φ k (M * rotM c s) = (⟨c, s⟩ : ℂ) ^ k * member ψ φ k M := by
  rw [member, member, core_mul_rotM φ k c s h, Matrix.det_mul, det_rotM c s h, mul_one]
  ring

private def memberE (ψ φ : ℝ → ℝ) (k : ℕ) : (Fin 2 → Fin 2 → ℝ) → ℂ := fun M => member ψ φ k (Matrix.of M)

private theorem entrySlice_unitFamily_memberE (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) (g : GL (Fin 2) ℝ) :
    entrySlice (unitFamily (memberE ψ φ k)) p g = member ψ φ k (g : Matrix (Fin 2) (Fin 2) ℝ) := rfl

private theorem member_type (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) (k₁ k₂ : rowIsometrySubgroup₀ ℝ)
    (g : GL (Fin 2) ℝ) :
    entrySlice (unitFamily (memberE ψ φ k)) p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
      ((archWeightCharℝ (k : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (k : ℤ) k₂ : ℂˣ) : ℂ) *
        entrySlice (unitFamily (memberE ψ φ k)) p g := by
  obtain ⟨c₁, s₁, h₁, e₁⟩ := exists_rotM_eq k₁
  obtain ⟨c₂, s₂, h₂, e₂⟩ := exists_rotM_eq k₂
  rw [entrySlice_unitFamily_memberE, entrySlice_unitFamily_memberE, Units.val_mul, Units.val_mul, e₁, e₂,
    member_mul_rotM ψ φ k c₂ s₂ h₂, member_rotM_mul ψ φ k c₁ s₁ h₁, archWeightCharℝ_natCast_apply k k₁ e₁,
    archWeightCharℝ_natCast_apply k k₂ e₂]
  ring

private theorem member_neg (ψ φ : ℝ → ℝ) (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    member ψ φ k (-M) = (-1) ^ k * member ψ φ k M := by
  have hd : Matrix.det (-M) = Matrix.det M := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp only [Matrix.neg_apply]; ring
  have hn : nsq (-M) = nsq M := by simp only [nsq, Matrix.neg_apply]; ring
  have hw : wt (-M) = -wt M := by
    apply Complex.ext <;> simp [wt, Matrix.neg_apply] <;> ring
  rw [member, member, core, core, hd, hn, hw, neg_pow]
  ring

private theorem core_smul (φ : ℝ → ℝ) (k : ℕ) {r : ℝ} (hr : r ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    core φ k (r • M) = (r : ℂ) ^ k * core φ k M := by
  have hd : Matrix.det (r • M) = r ^ 2 * Matrix.det M := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp only [Matrix.smul_apply, smul_eq_mul]; ring
  have hn : nsq (r • M) = r ^ 2 * nsq M := by simp only [nsq, Matrix.smul_apply, smul_eq_mul]; ring
  have hw : wt (r • M) = (r : ℂ) * wt M := by
    apply Complex.ext <;> simp [wt, Matrix.smul_apply, smul_eq_mul] <;> ring
  have hq : (nsq (r • M) - 2 * Matrix.det (r • M)) / Matrix.det (r • M) =
      (nsq M - 2 * Matrix.det M) / Matrix.det M := by
    rw [hd, hn, show r ^ 2 * nsq M - 2 * (r ^ 2 * Matrix.det M) = r ^ 2 * (nsq M - 2 * Matrix.det M) by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)
  rw [core, core, hq, hw, mul_pow]
  ring

private theorem norm_real_add_le (a : ℝ) (ha : 0 ≤ a) (w : ℂ) : ‖(a : ℂ) + w‖ ≤ a + ‖w‖ := by
  calc ‖(a : ℂ) + w‖ ≤ ‖(a : ℂ)‖ + ‖w‖ := norm_add_le _ _
    _ = a + ‖w‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

private theorem norm_add_pow_sub_pow_le (a : ℝ) (ha : 0 ≤ a) (w : ℂ) (k : ℕ) :
    ‖((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1)‖ ≤ (k + 1) * ‖w‖ * (a + ‖w‖) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ((a : ℂ) + w) ^ (k + 1 + 1) - (a : ℂ) ^ (k + 1 + 1) =
        ((a : ℂ) + w) * (((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1)) + w * (a : ℂ) ^ (k + 1) := by
      ring
    have hA : 0 ≤ a + ‖w‖ := add_nonneg ha (norm_nonneg w)
    have hpow : a ^ (k + 1) ≤ (a + ‖w‖) ^ (k + 1) :=
      pow_le_pow_left₀ ha (le_add_of_nonneg_right (norm_nonneg w)) (k + 1)
    have hna : ‖(a : ℂ) ^ (k + 1)‖ = a ^ (k + 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    have hdiff : 0 ≤ ‖((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1)‖ := norm_nonneg _
    calc ‖((a : ℂ) + w) ^ (k + 1 + 1) - (a : ℂ) ^ (k + 1 + 1)‖
        ≤ ‖((a : ℂ) + w) * (((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1))‖ + ‖w * (a : ℂ) ^ (k + 1)‖ := by
          rw [e]; exact norm_add_le _ _
      _ = ‖(a : ℂ) + w‖ * ‖((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1)‖ + ‖w‖ * a ^ (k + 1) := by
          rw [norm_mul, norm_mul, hna]
      _ ≤ (a + ‖w‖) * ((k + 1) * ‖w‖ * (a + ‖w‖) ^ k) + ‖w‖ * (a + ‖w‖) ^ (k + 1) :=
          add_le_add (mul_le_mul (norm_real_add_le a ha w) ih hdiff hA)
            (mul_le_mul_of_nonneg_left hpow (norm_nonneg w))
      _ = (↑(k + 1) + 1) * ‖w‖ * (a + ‖w‖) ^ (k + 1) := by
          rw [pow_succ]; push_cast; ring

private theorem re_pow_ge_of_abs_im_le (a b : ℝ) (ha : 0 < a) (k : ℕ)
    (hb : |b| ≤ a / (2 ^ (k + 3) * (k + 1))) :
    (7 / 8 : ℝ) * a ^ (k + 1) ≤ ((⟨a, b⟩ : ℂ) ^ (k + 1)).re := by
  have hk : (0 : ℝ) < 2 ^ (k + 3) * (k + 1) := by positivity
  have hk1 : (1 : ℝ) ≤ 2 ^ (k + 3) * (k + 1) := by
    have h2 : (1 : ℝ) ≤ 2 ^ (k + 3) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ (k : ℝ) + 1 := by simp
    nlinarith
  have hb' : |b| * (2 ^ (k + 3) * (k + 1)) ≤ a := (le_div_iff₀ hk).mp hb
  have hba : |b| ≤ a := by nlinarith [abs_nonneg b]
  set w : ℂ := (b : ℂ) * Complex.I with hw
  have hz : (⟨a, b⟩ : ℂ) = (a : ℂ) + w := by
    apply Complex.ext <;> simp [hw]
  have hnw : ‖w‖ = |b| := by
    rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  set D : ℂ := ((a : ℂ) + w) ^ (k + 1) - (a : ℂ) ^ (k + 1) with hD
  have hmain : ‖D‖ ≤ (k + 1) * |b| * (a + |b|) ^ k := by
    have h := norm_add_pow_sub_pow_le a ha.le w k
    rwa [hnw] at h
  have h1 : (a + |b|) ^ k ≤ (2 * a) ^ k :=
    pow_le_pow_left₀ (add_nonneg ha.le (abs_nonneg b)) (by linarith) k
  have h2 : (k + 1) * |b| ≤ a / 2 ^ (k + 3) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hb']
  have herr : (k + 1) * |b| * (a + |b|) ^ k ≤ a ^ (k + 1) / 8 := by
    calc (k + 1) * |b| * (a + |b|) ^ k ≤ (a / 2 ^ (k + 3)) * (2 * a) ^ k :=
          mul_le_mul h2 h1 (pow_nonneg (add_nonneg ha.le (abs_nonneg b)) k) (by positivity)
      _ = a ^ (k + 1) / 8 := by
          rw [mul_pow]
          field_simp
          ring
  have hre : a ^ (k + 1) - ‖D‖ ≤ (((a : ℂ) + w) ^ (k + 1)).re := by
    have hsplit : ((a : ℂ) + w) ^ (k + 1) = (a : ℂ) ^ (k + 1) + D := by rw [hD]; ring
    have hare : ((a : ℂ) ^ (k + 1)).re = a ^ (k + 1) := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hDre : -‖D‖ ≤ D.re := (abs_le.mp (Complex.abs_re_le_norm D)).1
    rw [hsplit, Complex.add_re, hare]
    linarith
  rw [hz]
  linarith

private def detE (M : Fin 2 → Fin 2 → ℝ) : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0

private def nsqE (M : Fin 2 → Fin 2 → ℝ) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

private def wtE (M : Fin 2 → Fin 2 → ℝ) : ℂ := ⟨M 0 0 + M 1 1, M 0 1 - M 1 0⟩

private theorem det_of (M : Fin 2 → Fin 2 → ℝ) : Matrix.det (Matrix.of M) = detE M := by
  simp [Matrix.det_fin_two, detE]

private theorem nsq_of (M : Fin 2 → Fin 2 → ℝ) : nsq (Matrix.of M) = nsqE M := rfl

private theorem wt_of (M : Fin 2 → Fin 2 → ℝ) : wt (Matrix.of M) = wtE M := rfl

private theorem memberE_eq (ψ φ : ℝ → ℝ) (k : ℕ) (M : Fin 2 → Fin 2 → ℝ) :
    memberE ψ φ k M = (ψ (detE M) : ℂ) * ((φ ((nsqE M - 2 * detE M) / detE M) : ℂ) * wtE M ^ k) := by
  simp only [memberE, member, core, det_of, nsq_of, wt_of]

private theorem contDiff_coord (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ => M i j :=
  contDiff_apply_apply ℝ ℝ i j

private theorem contDiff_detE : ContDiff ℝ (⊤ : ℕ∞) detE := by
  unfold detE
  exact ((contDiff_coord 0 0).mul (contDiff_coord 1 1)).sub ((contDiff_coord 0 1).mul (contDiff_coord 1 0))

private theorem contDiff_nsqE : ContDiff ℝ (⊤ : ℕ∞) nsqE := by
  unfold nsqE
  exact ((((contDiff_coord 0 0).pow 2).add ((contDiff_coord 0 1).pow 2)).add ((contDiff_coord 1 0).pow 2)).add
    ((contDiff_coord 1 1).pow 2)

private theorem wtE_eq (M : Fin 2 → Fin 2 → ℝ) :
    wtE M = ((M 0 0 + M 1 1 : ℝ) : ℂ) + ((M 0 1 - M 1 0 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [wtE]

private theorem contDiff_wtE : ContDiff ℝ (⊤ : ℕ∞) wtE := by
  have h : wtE = fun M => ((M 0 0 + M 1 1 : ℝ) : ℂ) + ((M 0 1 - M 1 0 : ℝ) : ℂ) * Complex.I := funext wtE_eq
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_coord 0 0).add (contDiff_coord 1 1))).add
    ((Complex.ofRealCLM.contDiff.comp ((contDiff_coord 0 1).sub (contDiff_coord 1 0))).mul contDiff_const)

private theorem continuous_detE : Continuous detE := contDiff_detE.continuous

private theorem continuous_nsqE : Continuous nsqE := contDiff_nsqE.continuous

private structure Profiles (ψ φ : ℝ → ℝ) (δ Δ ε : ℝ) : Prop where
  hδ : 0 < δ
  hψ : ContDiff ℝ (⊤ : ℕ∞) ψ
  hψ0 : ∀ x, x ≤ δ → ψ x = 0
  hψΔ : ∀ x, Δ ≤ x → ψ x = 0
  hφ : ContDiff ℝ (⊤ : ℕ∞) φ
  hε : 0 < ε
  hφε : ∀ x, ε ≤ x → φ x = 0

private theorem contDiff_memberE {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (memberE ψ φ k) := by

  have hg : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ => ψ (detE M) * φ ((nsqE M - 2 * detE M) / detE M) := by
    rw [contDiff_iff_contDiffAt]
    intro M
    by_cases hM : detE M < δ
    ·
      have hev : (fun N : Fin 2 → Fin 2 → ℝ => ψ (detE N) * φ ((nsqE N - 2 * detE N) / detE N)) =ᶠ[nhds M]
          fun _ => 0 := by
        have ho : IsOpen {N : Fin 2 → Fin 2 → ℝ | detE N < δ} := isOpen_lt continuous_detE continuous_const
        filter_upwards [ho.mem_nhds hM] with N hN
        rw [hP.hψ0 _ (le_of_lt hN), zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    · have hne : detE M ≠ 0 := by
        have : δ ≤ detE M := le_of_not_gt hM
        linarith [hP.hδ]
      exact ((hP.hψ.comp contDiff_detE).contDiffAt).mul
        ((hP.hφ.contDiffAt).comp M
          (((contDiff_nsqE.sub (contDiff_const.mul contDiff_detE)).contDiffAt).div contDiff_detE.contDiffAt hne))
  have hgC : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ =>
      ((ψ (detE M) * φ ((nsqE M - 2 * detE M) / detE M) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hg
  have h : memberE ψ φ k = fun M =>
      ((ψ (detE M) * φ ((nsqE M - 2 * detE M) / detE M) : ℝ) : ℂ) * wtE M ^ k := by
    funext M; rw [memberE_eq]; push_cast; ring
  rw [h]
  exact hgC.mul (contDiff_wtE.pow k)

private theorem detE_mem_of_memberE_ne_zero {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) {k : ℕ}
    {M : Fin 2 → Fin 2 → ℝ} (hM : memberE ψ φ k M ≠ 0) :
    δ < detE M ∧ detE M < Δ ∧ nsqE M < (2 + ε) * Δ := by
  rw [memberE_eq] at hM
  have hψne : ψ (detE M) ≠ 0 := by
    intro h; apply hM; rw [h]; simp
  have hφne : φ ((nsqE M - 2 * detE M) / detE M) ≠ 0 := by
    intro h; apply hM; rw [h]; simp
  have h1 : δ < detE M := lt_of_not_ge fun h => hψne (hP.hψ0 _ h)
  have h2 : detE M < Δ := lt_of_not_ge fun h => hψne (hP.hψΔ _ h)
  have hpos : 0 < detE M := hP.hδ.trans h1
  have h3 : (nsqE M - 2 * detE M) / detE M < ε := lt_of_not_ge fun h => hφne (hP.hφε _ h)
  rw [div_lt_iff₀ hpos] at h3
  refine ⟨h1, h2, ?_⟩
  have hε : ε * detE M ≤ ε * Δ := mul_le_mul_of_nonneg_left h2.le hP.hε.le
  nlinarith

private theorem hasCompactSupport_memberE {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    HasCompactSupport (memberE ψ φ k) := by
  set B : ℝ := (2 + ε) * Δ with hB
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin 2 → Fin 2 → ℝ) (Real.sqrt B)) ?_
  intro M hM
  rw [Function.mem_support] at hM
  obtain ⟨-, -, hn⟩ := detE_mem_of_memberE_ne_zero hP hM
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)]
  intro j
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have h00 : M 0 0 ^ 2 ≤ nsqE M := by unfold nsqE; nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 1 0), sq_nonneg (M 1 1)]
  have h01 : M 0 1 ^ 2 ≤ nsqE M := by unfold nsqE; nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0), sq_nonneg (M 1 1)]
  have h10 : M 1 0 ^ 2 ≤ nsqE M := by unfold nsqE; nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 0 1), sq_nonneg (M 1 1)]
  have h11 : M 1 1 ^ 2 ≤ nsqE M := by unfold nsqE; nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 0 1), sq_nonneg (M 1 0)]
  have hij : M i j ^ 2 ≤ nsqE M := by
    fin_cases i <;> fin_cases j <;> first | exact h00 | exact h01 | exact h10 | exact h11
  linarith

private theorem tsupport_memberE {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    tsupport (memberE ψ φ k) ⊆ {M | IsUnit (Matrix.det (Matrix.of M))} := by
  have hcl : IsClosed {M : Fin 2 → Fin 2 → ℝ | δ ≤ detE M} := isClosed_le continuous_const continuous_detE
  have hsub : Function.support (memberE ψ φ k) ⊆ {M | δ ≤ detE M} := fun M hM =>
    (detE_mem_of_memberE_ne_zero hP (Function.mem_support.mp hM)).1.le
  intro M hM
  have hM' : δ ≤ detE M := (closure_minimal hsub hcl) hM
  rw [Set.mem_setOf_eq, det_of, isUnit_iff_ne_zero]
  exact ne_of_gt (hP.hδ.trans_le hM')

private theorem coe_rotation (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM (Real.cos θ) (Real.sin θ) := rfl

private theorem rotM_mul_rotM_neg (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : rotM c s * rotM c (-s) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination h

private theorem coe_rotation_inv (θ : ℝ) :
    (((rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM (Real.cos θ) (-Real.sin θ) := by
  rw [Matrix.coe_units_inv, coe_rotation]
  exact Matrix.inv_eq_right_inv (rotM_mul_rotM_neg _ _ (Real.cos_sq_add_sin_sq θ))

private theorem coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] := rfl

private theorem member_triangular (ψ φ : ℝ → ℝ) (k : ℕ) (a₁ a₂ u : ℝ) :
    member ψ φ k !![a₁, u; 0, a₂] =
      (ψ (a₁ * a₂) : ℂ) * ((φ (((a₁ - a₂) ^ 2 + u ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, u⟩ : ℂ) ^ k) := by
  have hd : Matrix.det !![a₁, u; 0, a₂] = a₁ * a₂ := by simp [Matrix.det_fin_two_of]
  have hn : nsq !![a₁, u; 0, a₂] = a₁ ^ 2 + u ^ 2 + 0 ^ 2 + a₂ ^ 2 := by
    simp only [nsq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  have hw : wt !![a₁, u; 0, a₂] = ⟨a₁ + a₂, u⟩ := by
    apply Complex.ext <;> simp [wt]
  rw [member, core, hd, hn, hw,
    show (a₁ ^ 2 + u ^ 2 + 0 ^ 2 + a₂ ^ 2 - 2 * (a₁ * a₂)) / (a₁ * a₂) = ((a₁ - a₂) ^ 2 + u ^ 2) / (a₁ * a₂) by ring]

private theorem member_conj_rotation (ψ φ : ℝ → ℝ) (k : ℕ) (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    member ψ φ k (rotM (Real.cos θ) (Real.sin θ) * M * rotM (Real.cos θ) (-Real.sin θ)) = member ψ φ k M := by
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hc' : Real.cos θ ^ 2 + (-Real.sin θ) ^ 2 = 1 := by rw [neg_sq]; exact hc
  have h1 : (⟨Real.cos θ, -Real.sin θ⟩ : ℂ) * ⟨Real.cos θ, Real.sin θ⟩ = 1 := by
    apply Complex.ext
    · simp; nlinarith [hc]
    · simp; ring
  rw [member_mul_rotM ψ φ k _ _ hc', member_rotM_mul ψ φ k _ _ hc, ← mul_assoc, ← mul_pow, h1, one_pow,
    one_mul]

private theorem splitTransform_member (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) :
    splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) a₁ a₂ =
      ∫ u : ℝ, (ψ (a₁ * a₂) : ℂ) * ((φ (((a₁ - a₂) ^ 2 + u ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, u⟩ : ℂ) ^ k) := by
  have hθ : ∀ θ u : ℝ, entrySlice (unitFamily (memberE ψ φ k)) p
      (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) =
        (ψ (a₁ * a₂) : ℂ) * ((φ (((a₁ - a₂) ^ 2 + u ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, u⟩ : ℂ) ^ k) := by
    intro θ u
    rw [entrySlice_unitFamily_memberE, Units.val_mul, Units.val_mul, coe_rotation, coe_rotation_inv,
      coe_upperTriangular, member_conj_rotation, member_triangular]
  rw [splitTransform, dif_pos h]
  simp_rw [hθ]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

private def fibreFun (φ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∫ v : ℝ, (φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℂ) * (⟨2 * Real.cosh t, v⟩ : ℂ) ^ k

private theorem splitTransform_member_exp (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) (r * Real.exp t) (r * Real.exp (-t)) =
      (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1) * fibreFun φ k t := by
  have hprod : r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 := by
    rw [show r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 * (Real.exp t * Real.exp (-t)) by ring,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h : r * Real.exp t * (r * Real.exp (-t)) ≠ 0 := by rw [hprod]; positivity
  have hdiff : r * Real.exp t - r * Real.exp (-t) = 2 * r * Real.sinh t := by rw [Real.sinh_eq]; ring
  have hsum : r * Real.exp t + r * Real.exp (-t) = 2 * r * Real.cosh t := by rw [Real.cosh_eq]; ring
  rw [splitTransform_member ψ φ k p h]
  simp only [hprod, hdiff, hsum]

  have hsub := Measure.integral_comp_mul_left
    (fun u : ℝ => (ψ (r ^ 2) : ℂ) * ((φ (((2 * r * Real.sinh t) ^ 2 + u ^ 2) / r ^ 2) : ℂ) *
      (⟨2 * r * Real.cosh t, u⟩ : ℂ) ^ k)) r
  have hr0 : r ≠ 0 := hr.ne'
  have habs : |r⁻¹| = r⁻¹ := abs_of_pos (inv_pos.mpr hr)
  rw [habs] at hsub

  have hG : (∫ u : ℝ, (ψ (r ^ 2) : ℂ) * ((φ (((2 * r * Real.sinh t) ^ 2 + u ^ 2) / r ^ 2) : ℂ) *
      (⟨2 * r * Real.cosh t, u⟩ : ℂ) ^ k)) =
      r • ∫ v : ℝ, (ψ (r ^ 2) : ℂ) * ((φ (((2 * r * Real.sinh t) ^ 2 + (r * v) ^ 2) / r ^ 2) : ℂ) *
        (⟨2 * r * Real.cosh t, r * v⟩ : ℂ) ^ k) := by
    rw [hsub, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  rw [hG, Complex.real_smul, fibreFun]

  have hpt : ∀ v : ℝ, (ψ (r ^ 2) : ℂ) * ((φ (((2 * r * Real.sinh t) ^ 2 + (r * v) ^ 2) / r ^ 2) : ℂ) *
      (⟨2 * r * Real.cosh t, r * v⟩ : ℂ) ^ k) =
      (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ k * ((φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℂ) * (⟨2 * Real.cosh t, v⟩ : ℂ) ^ k) := by
    intro v
    have ha : ((2 * r * Real.sinh t) ^ 2 + (r * v) ^ 2) / r ^ 2 = 4 * Real.sinh t ^ 2 + v ^ 2 := by
      field_simp
      ring
    have hb : (⟨2 * r * Real.cosh t, r * v⟩ : ℂ) = (r : ℂ) * ⟨2 * Real.cosh t, v⟩ := by
      apply Complex.ext <;> simp; ring
    rw [ha, hb, mul_pow]
    ring
  simp_rw [hpt]
  have hI : (∫ v : ℝ, (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ k *
      ((φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℂ) * (⟨2 * Real.cosh t, v⟩ : ℂ) ^ k)) =
      (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ k *
        ∫ v : ℝ, (φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℂ) * (⟨2 * Real.cosh t, v⟩ : ℂ) ^ k :=
    integral_const_mul _ _
  rw [hI]
  ring

private theorem splitTransform_member_neg (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) :
    splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) (-a₁) (-a₂) =
      (-1 : ℂ) ^ k * splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) a₁ a₂ := by
  have h' : -a₁ * -a₂ ≠ 0 := by rwa [neg_mul_neg]
  rw [splitTransform_member ψ φ k p h', splitTransform_member ψ φ k p h]
  have hpt : ∀ u : ℝ, (ψ (-a₁ * -a₂) : ℂ) *
      ((φ (((-a₁ - -a₂) ^ 2 + u ^ 2) / (-a₁ * -a₂)) : ℂ) * (⟨-a₁ + -a₂, u⟩ : ℂ) ^ k) =
      (-1 : ℂ) ^ k * ((ψ (a₁ * a₂) : ℂ) *
        ((φ (((a₁ - a₂) ^ 2 + (-u) ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, -u⟩ : ℂ) ^ k)) := by
    intro u
    have e1 : -a₁ * -a₂ = a₁ * a₂ := neg_mul_neg a₁ a₂
    have e2 : (-a₁ - -a₂) ^ 2 = (a₁ - a₂) ^ 2 := by ring
    have e3 : (⟨-a₁ + -a₂, u⟩ : ℂ) = -⟨a₁ + a₂, -u⟩ := by
      apply Complex.ext
      · show -a₁ + -a₂ = -(a₁ + a₂); ring
      · show u = -(-u); ring
    rw [e1, e2, e3, neg_pow, neg_sq]
    ring
  simp_rw [hpt]
  have hI : (∫ u : ℝ, (-1 : ℂ) ^ k * ((ψ (a₁ * a₂) : ℂ) *
      ((φ (((a₁ - a₂) ^ 2 + (-u) ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, -u⟩ : ℂ) ^ k))) =
      (-1 : ℂ) ^ k * ∫ u : ℝ, (ψ (a₁ * a₂) : ℂ) *
        ((φ (((a₁ - a₂) ^ 2 + (-u) ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, -u⟩ : ℂ) ^ k) :=
    integral_const_mul _ _
  rw [hI]
  congr 1
  exact integral_neg_eq_self (fun u : ℝ => (ψ (a₁ * a₂) : ℂ) *
    ((φ (((a₁ - a₂) ^ 2 + u ^ 2) / (a₁ * a₂)) : ℂ) * (⟨a₁ + a₂, u⟩ : ℂ) ^ k)) volume

private theorem pairing_member (ψ φ : ℝ → ℝ) (k : ℕ) (p : Unit) (κ : ℝ)
    (hsurv : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∀ r : ℝ, 0 < r →
      (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice (unitFamily (memberE ψ φ k)) p) r θ *
          (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        -(κ : ℂ) * (1 / r : ℂ) *
          ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
            (splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) (r * Real.exp t) (r * Real.exp (-t)) +
              (-1 : ℂ) ^ j * splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p)
                (-(r * Real.exp t)) (-(r * Real.exp (-t)))))
    {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k + 1) (hpar : Even (j + k)) {r : ℝ} (hr : 0 < r) :
    discreteSeriesPairing j (splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p))
        (ellipticTransform (entrySlice (unitFamily (memberE ψ φ k)) p)) r =
      -2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ k *
        ((κ : ℂ) * (∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) * fibreFun φ k t) +
          2 * Real.pi * ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) * fibreFun φ k t) := by

  have hbr : ∀ t : ℝ,
      splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p)
          (-(r * Real.exp t)) (-(r * Real.exp (-t))) =
      (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * fibreFun φ k t := by
    intro t
    have h0 : r * Real.exp t * (r * Real.exp (-t)) ≠ 0 := by positivity
    have hjk' : (-1 : ℂ) ^ j * (-1 : ℂ) ^ k = 1 := by rw [← pow_add]; exact hpar.neg_one_pow
    rw [splitTransform_member_neg ψ φ k p h0, splitTransform_member_exp ψ φ k p hr t, ← mul_assoc, hjk', one_mul]
    ring
  rw [discreteSeriesPairing, hsurv j hj2 hjk r hr]
  simp_rw [hbr]
  have hX : ∀ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
      ((2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * fibreFun φ k t)
      = (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * ((Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) * fibreFun φ k t) := by
    intro t; ring
  have hY : ∀ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      ((2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * fibreFun φ k t)
      = (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) * fibreFun φ k t) := by
    intro t; ring
  simp_rw [hX, hY]
  have hIX : (∫ t : ℝ, (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) *
      ((Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) * fibreFun φ k t)) =
      (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) * ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) * fibreFun φ k t :=
    integral_const_mul _ _
  have hIY : (∫ t : ℝ, (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) *
      ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) * fibreFun φ k t)) =
      (2 * (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k + 1)) *
        ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) * fibreFun φ k t :=
    integral_const_mul _ _
  rw [hIX, hIY]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

private theorem eqOn_Ioo_of_modes_eq (A B : ℝ → ℂ) (K : ℝ) (hA : ContinuousOn A (Set.Ioo 0 Real.pi))
    (hAb : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ‖A θ‖ ≤ K) (hB : ContinuousOn B (Set.Ioo 0 Real.pi))
    (hBi : IntervalIntegrable B volume 0 Real.pi)
    (hmodes : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi, A θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) =
      ∫ θ in (0 : ℝ)..Real.pi, B θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, A θ = B θ := by

  have hU : ∀ j : ℕ, Continuous fun θ : ℝ => (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) := fun j =>
    Complex.continuous_ofReal.comp ((Chebyshev.U ℝ (j : ℤ)).continuous.comp Real.continuous_cos)

  have hAi : IntervalIntegrable A volume 0 Real.pi := by
    have hIoo : IntegrableOn A (Set.Ioo 0 Real.pi) volume := by
      have hbdd : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) Real.pi)), ‖A θ‖ ≤ K :=
        (ae_restrict_mem measurableSet_Ioo).mono hAb
      exact ⟨hA.aestronglyMeasurable measurableSet_Ioo,
        HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioo_lt_top hbdd⟩
    rw [intervalIntegrable_iff, Set.uIoc_of_le Real.pi_pos.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).mpr hIoo
  have hAU : ∀ j : ℕ, IntervalIntegrable
      (fun θ : ℝ => A θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi :=
    fun j => hAi.mul_continuousOn (hU j).continuousOn
  have hBU : ∀ j : ℕ, IntervalIntegrable
      (fun θ : ℝ => B θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi :=
    fun j => hBi.mul_continuousOn (hU j).continuousOn

  have hg : ∀ j : ℕ,
      ∫ θ in (0 : ℝ)..Real.pi, (A θ - B θ) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0 := by
    intro j
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hAU j) (hBU j), hmodes j, sub_self]
  have h := Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero (fun θ => A θ - B θ)
    (hA.sub hB) (hAi.sub hBi) hg
  intro θ hθ
  exact sub_eq_zero.mp (h θ hθ)

private theorem splitTransform_axes (f : GL (Fin 2) ℝ → ℂ) {a₁ a₂ : ℝ} (h : a₁ * a₂ = 0) :
    splitTransform f a₁ a₂ = 0 := by
  rw [splitTransform, dif_neg (not_not.mpr h)]

private def memberSplit (ψ φ : ℝ → ℝ) (k : ℕ) : ℝ × ℝ × Unit → ℂ :=
  fun q => splitTransform (entrySlice (unitFamily (memberE ψ φ k)) q.2.2) q.1 q.2.1

private theorem memberSplit_admissible {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (memberSplit ψ φ k) ∧ HasCompactSupport (memberSplit ψ φ k) ∧
      tsupport (memberSplit ψ φ k) ⊆ {q | q.1 * q.2.1 ≠ 0} ∧
      (∀ (a₁ a₂ : ℝ) (p : Unit), memberSplit ψ φ k (a₂, a₁, p) = memberSplit ψ φ k (a₁, a₂, p)) ∧
      ∀ (a₁ a₂ : ℝ) (p : Unit), memberSplit ψ φ k (-a₁, -a₂, p) = (-1 : ℂ) ^ k * memberSplit ψ φ k (a₁, a₂, p) := by
  have h := contDiff_splitTransform_entrySlice Unit (unitFamily (memberE ψ φ k))
    (contDiff_unitFamily (contDiff_memberE hP k)) (hasCompactSupport_unitFamily (hasCompactSupport_memberE hP k))
    (tsupport_unitFamily (tsupport_memberE hP k))
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  intro a₁ a₂ p
  show splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) (-a₁) (-a₂) =
    (-1 : ℂ) ^ k * splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) a₁ a₂
  by_cases h0 : a₁ * a₂ = 0
  · rw [splitTransform_axes _ h0, splitTransform_axes _ (by rw [neg_mul_neg]; exact h0), mul_zero]
  · exact splitTransform_member_neg ψ φ k p h0

private structure IsRealiser (m : ℤ) (sgn : ℂ) (I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ)) : Prop where
  lin : ∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M
  real : ∀ H : ℝ × ℝ × Unit → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
    tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
    (∀ (a₁ a₂ : ℝ) (p : Unit), H (a₂, a₁, p) = H (a₁, a₂, p)) →
    (∀ (a₁ a₂ : ℝ) (p : Unit), H (-a₁, -a₂, p) = sgn * H (a₁, a₂, p)) →
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
    HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
    tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
      {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
    (∀ (p : Unit) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
          ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ m k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ m k₂ : ℂˣ) : ℂ) *
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
    ∀ (p : Unit) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
      splitTransform
          (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × Unit => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
          a₁ a₂ = H (a₁, a₂, p)

private theorem exists_isRealiser_zero : ∃ I, IsRealiser 0 1 I := by
  obtain ⟨I, hL, hI⟩ := exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq Unit
  exact ⟨I, hL, fun H h1 h2 h3 h4 h5 => hI H h1 h2 h3 h4 fun a₁ a₂ p => by rw [h5 a₁ a₂ p, one_mul]⟩

private theorem exists_isRealiser_one : ∃ I, IsRealiser 1 (-1) I := by
  obtain ⟨I, hL, hI⟩ := exists_linear_entrySlice_archWeightChar_one_splitTransform_eq Unit
  exact ⟨I, hL, fun H h1 h2 h3 h4 h5 => hI H h1 h2 h3 h4 fun a₁ a₂ p => by rw [h5 a₁ a₂ p, neg_one_mul]⟩

private def realiser0 : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ) := Classical.choose exists_isRealiser_zero

private def realiser1 : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ) := Classical.choose exists_isRealiser_one

private theorem realiser0_spec : IsRealiser 0 1 realiser0 := Classical.choose_spec exists_isRealiser_zero

private theorem realiser1_spec : IsRealiser 1 (-1) realiser1 := Classical.choose_spec exists_isRealiser_one

open Classical in

private def realiser (k : ℕ) : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ) :=
  if Even k then realiser0 else realiser1

private theorem realiser_spec (k : ℕ) : IsRealiser ((k % 2 : ℕ) : ℤ) ((-1 : ℂ) ^ k) (realiser k) := by
  unfold realiser
  by_cases h : Even k
  · rw [if_pos h, Nat.even_iff.mp h, h.neg_one_pow, Nat.cast_zero]
    exact realiser0_spec
  · have h' : Odd k := Nat.not_even_iff_odd.mp h
    rw [if_neg h, Nat.odd_iff.mp h', h'.neg_one_pow, Nat.cast_one]
    exact realiser1_spec

private def memberCorr (ψ φ : ℝ → ℝ) (k : ℕ) : (Fin 2 → Fin 2 → ℝ) × Unit → ℂ :=
  fun q => realiser k (fun a : ℝ × ℝ => memberSplit ψ φ k (a.1, a.2, q.2)) q.1

private def adjuster (ψ φ : ℝ → ℝ) (k : ℕ) : (Fin 2 → Fin 2 → ℝ) × Unit → ℂ :=
  fun q => unitFamily (memberE ψ φ k) q - memberCorr ψ φ k q

private theorem memberCorr_props {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (memberCorr ψ φ k) ∧ HasCompactSupport (memberCorr ψ φ k) ∧
      tsupport (memberCorr ψ φ k) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
      (∀ (p : Unit) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        entrySlice (memberCorr ψ φ k) p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ ((k % 2 : ℕ) : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ ((k % 2 : ℕ) : ℤ) k₂ : ℂˣ) : ℂ) *
            entrySlice (memberCorr ψ φ k) p g) ∧
      ∀ (p : Unit) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
        splitTransform (entrySlice (memberCorr ψ φ k) p) a₁ a₂ = memberSplit ψ φ k (a₁, a₂, p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := memberSplit_admissible hP k
  exact (realiser_spec k).real (memberSplit ψ φ k) h1 h2 h3 h4 h5

private theorem contDiff_adjuster {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (adjuster ψ φ k) :=
  (contDiff_unitFamily (contDiff_memberE hP k)).sub (memberCorr_props hP k).1

private theorem hasCompactSupport_adjuster {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    HasCompactSupport (adjuster ψ φ k) := by
  have h : adjuster ψ φ k = unitFamily (memberE ψ φ k) + -memberCorr ψ φ k := by
    funext q; simp only [adjuster, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  rw [h]
  exact (hasCompactSupport_unitFamily (hasCompactSupport_memberE hP k)).add (memberCorr_props hP k).2.1.neg

private theorem tsupport_adjuster {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) :
    tsupport (adjuster ψ φ k) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  intro q hq
  have hs : Function.support (adjuster ψ φ k) ⊆
      Function.support (unitFamily (memberE ψ φ k)) ∪ Function.support (memberCorr ψ φ k) :=
    Function.support_sub _ _
  have hq' : q ∈ tsupport (unitFamily (memberE ψ φ k)) ∪ tsupport (memberCorr ψ φ k) := by
    have h := closure_mono hs hq
    rwa [closure_union] at h
  rcases hq' with h | h
  · exact tsupport_unitFamily (tsupport_memberE hP k) h
  · exact (memberCorr_props hP k).2.2.1 h

private theorem splitTransform_adjuster {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ)
    (p : Unit) {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) : splitTransform (entrySlice (adjuster ψ φ k) p) a₁ a₂ = 0 := by
  have hc := memberCorr_props hP k
  have hΨc : HasCompactSupport ((-1 : ℂ) • memberCorr ψ φ k) :=
    HasCompactSupport.of_support_subset_isCompact hc.2.1 fun q hq => subset_tsupport _
      (Function.mem_support.mpr fun h0 => (Function.mem_support.mp hq) (by rw [Pi.smul_apply, h0, smul_zero]))
  have hsub := splitTransform_entrySlice_add (unitFamily (memberE ψ φ k)) ((-1 : ℂ) • memberCorr ψ φ k)
    (contDiff_unitFamily (contDiff_memberE hP k)).continuous
    (hasCompactSupport_unitFamily (hasCompactSupport_memberE hP k)) (hc.1.continuous.const_smul (-1 : ℂ)) hΨc p a₁ a₂
  have hsm := splitTransform_entrySlice_smul (-1 : ℂ) (memberCorr ψ φ k) p a₁ a₂
  have hfun : adjuster ψ φ k = unitFamily (memberE ψ φ k) + (-1 : ℂ) • memberCorr ψ φ k := by
    funext q; simp only [adjuster, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hfun, hsub, hsm, hc.2.2.2.2 p a₁ a₂ h]
  show splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) a₁ a₂ +
    (-1 : ℂ) * splitTransform (entrySlice (unitFamily (memberE ψ φ k)) p) a₁ a₂ = 0
  ring

private def fibreIntegrand (φ : ℝ → ℝ) (k : ℕ) (t v : ℝ) : ℂ :=
  (φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℂ) * (⟨2 * Real.cosh t, v⟩ : ℂ) ^ k

private theorem fibreFun_eq (φ : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    fibreFun φ k t = ∫ v : ℝ, fibreIntegrand φ k t v := rfl

private theorem mk_eq_add_mul_I (a b : ℝ) : (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private theorem fibreIntegrand_eq_form (φ : ℝ → ℝ) (k : ℕ) (t v : ℝ) :
    fibreIntegrand φ k t v =
      ((φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℝ) : ℂ) * (((2 * Real.cosh t : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ k := by
  simp only [fibreIntegrand, mk_eq_add_mul_I, Complex.ofReal_mul, Complex.ofReal_ofNat]

private theorem continuous_fibreIntegrand_left (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℕ) (v : ℝ) :
    Continuous fun t : ℝ => fibreIntegrand φ k t v := by
  have h : (fun t : ℝ => fibreIntegrand φ k t v) = fun t : ℝ =>
      ((φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℝ) : ℂ) * (((2 * Real.cosh t : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ k :=
    funext fun t => fibreIntegrand_eq_form φ k t v
  rw [h]
  have hφ' : Continuous fun t : ℝ => φ (4 * Real.sinh t ^ 2 + v ^ 2) := hφ.comp (by fun_prop)
  exact (Complex.continuous_ofReal.comp hφ').mul (by fun_prop)

private theorem continuous_fibreIntegrand_right (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℕ) (t : ℝ) :
    Continuous fun v : ℝ => fibreIntegrand φ k t v := by
  have h : (fun v : ℝ => fibreIntegrand φ k t v) = fun v : ℝ =>
      ((φ (4 * Real.sinh t ^ 2 + v ^ 2) : ℝ) : ℂ) * (((2 * Real.cosh t : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ k :=
    funext fun v => fibreIntegrand_eq_form φ k t v
  rw [h]
  have hφ' : Continuous fun v : ℝ => φ (4 * Real.sinh t ^ 2 + v ^ 2) := hφ.comp (by fun_prop)
  exact (Complex.continuous_ofReal.comp hφ').mul (by fun_prop)

private theorem fibreIntegrand_eq_zero (φ : ℝ → ℝ) (k : ℕ) {ε : ℝ} (hφε : ∀ x, ε ≤ x → φ x = 0) {t v : ℝ}
    (h : ε ≤ 4 * Real.sinh t ^ 2 + v ^ 2) : fibreIntegrand φ k t v = 0 := by
  simp [fibreIntegrand, hφε _ h]

private theorem two_cosh_le_of_window {ε' t : ℝ} (h : 4 * Real.sinh t ^ 2 ≤ ε') : 2 * Real.cosh t ≤ ε' / 2 + 2 := by
  have h1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have h2 : Real.cosh t ^ 2 = Real.sinh t ^ 2 + 1 := Real.cosh_sq t
  nlinarith

private theorem exists_bound (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℕ) {ε : ℝ} (hφε : ∀ x, ε ≤ x → φ x = 0) :
    ∃ s K : ℝ, 0 ≤ K ∧
      ∀ t v : ℝ, ‖fibreIntegrand φ k t v‖ ≤ Set.indicator (Set.Icc (-s) s) (fun _ => K) v := by
  set ε' : ℝ := max ε 0 with hε'
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hεε' : ε ≤ ε' := le_max_left _ _
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ε')).exists_bound_of_continuousOn hφ.continuousOn
  set s : ℝ := Real.sqrt ε' with hs
  set K : ℝ := max M 0 * (ε' / 2 + 2 + s) ^ k with hK
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (by positivity) _)
  refine ⟨s, K, hK0, fun t v => ?_⟩
  by_cases hwin : ε' ≤ 4 * Real.sinh t ^ 2 + v ^ 2
  · rw [fibreIntegrand_eq_zero φ k hφε (hεε'.trans hwin), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hK0) v
  · rw [not_le] at hwin
    have hsinh : 0 ≤ 4 * Real.sinh t ^ 2 := by positivity
    have hv2 : v ^ 2 ≤ ε' := by nlinarith
    have hvs : |v| ≤ s := Real.abs_le_sqrt hv2
    have hmem : v ∈ Set.Icc (-s) s := abs_le.mp hvs
    rw [Set.indicator_of_mem hmem]
    have harg : 4 * Real.sinh t ^ 2 + v ^ 2 ∈ Set.Icc (0 : ℝ) ε' := ⟨by positivity, hwin.le⟩
    have hφM : ‖φ (4 * Real.sinh t ^ 2 + v ^ 2)‖ ≤ max M 0 := (hM _ harg).trans (le_max_left _ _)
    have hcosh : 2 * Real.cosh t ≤ ε' / 2 + 2 := two_cosh_le_of_window (by nlinarith)
    have hcosh0 : 0 ≤ 2 * Real.cosh t := by positivity
    have hz : ‖(⟨2 * Real.cosh t, v⟩ : ℂ)‖ ≤ ε' / 2 + 2 + s := by
      calc ‖(⟨2 * Real.cosh t, v⟩ : ℂ)‖ ≤ |2 * Real.cosh t| + |v| := Complex.norm_le_abs_re_add_abs_im _
        _ = 2 * Real.cosh t + |v| := by rw [abs_of_nonneg hcosh0]
        _ ≤ ε' / 2 + 2 + s := add_le_add hcosh hvs
    have hzk : ‖(⟨2 * Real.cosh t, v⟩ : ℂ) ^ k‖ ≤ (ε' / 2 + 2 + s) ^ k := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hz k
    calc ‖fibreIntegrand φ k t v‖
        = ‖φ (4 * Real.sinh t ^ 2 + v ^ 2)‖ * ‖(⟨2 * Real.cosh t, v⟩ : ℂ) ^ k‖ := by
          rw [fibreIntegrand, norm_mul, Complex.norm_real]
      _ ≤ max M 0 * (ε' / 2 + 2 + s) ^ k :=
          mul_le_mul hφM hzk (norm_nonneg _) (le_max_right _ _)
      _ = K := hK.symm

private theorem integrable_bound (s K : ℝ) :
    Integrable (Set.indicator (Set.Icc (-s) s) (fun _ : ℝ => K)) :=
  (integrableOn_const (C := K) (s := Set.Icc (-s) s) (μ := (volume : Measure ℝ))
    (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc

private theorem integrable_fibreIntegrand (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℕ) {ε : ℝ}
    (hφε : ∀ x, ε ≤ x → φ x = 0) (t : ℝ) : Integrable (fun v : ℝ => fibreIntegrand φ k t v) := by
  obtain ⟨s, K, -, hb⟩ := exists_bound φ hφ k hφε
  exact (integrable_bound s K).mono' (continuous_fibreIntegrand_right φ hφ k t).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb t))

private theorem fibreFun_eq_zero (φ : ℝ → ℝ) (k : ℕ) {ε : ℝ} (hφε : ∀ x, ε ≤ x → φ x = 0) {t : ℝ}
    (ht : ε ≤ 4 * Real.sinh t ^ 2) : fibreFun φ k t = 0 := by
  rw [fibreFun_eq]
  have h : (fun v : ℝ => fibreIntegrand φ k t v) = fun _ => (0 : ℂ) := by
    funext v
    exact fibreIntegrand_eq_zero φ k hφε (ht.trans (le_add_of_nonneg_right (sq_nonneg v)))
  rw [h, integral_zero]

private theorem continuous_fibreFun (φ : ℝ → ℝ) (k : ℕ) (hφ : Continuous φ) {ε : ℝ} (hφε : ∀ x, ε ≤ x → φ x = 0) :
    Continuous (fibreFun φ k) := by
  obtain ⟨s, K, -, hb⟩ := exists_bound φ hφ k hφε
  show Continuous fun t : ℝ => ∫ v : ℝ, fibreIntegrand φ k t v
  exact continuous_of_dominated (fun t => (continuous_fibreIntegrand_right φ hφ k t).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall (hb t)) (integrable_bound s K)
    (Filter.Eventually.of_forall fun v => continuous_fibreIntegrand_left φ hφ k v)

private theorem hasCompactSupport_fibreFun (φ : ℝ → ℝ) (k : ℕ) (hφ : Continuous φ) {ε : ℝ}
    (hφε : ∀ x, ε ≤ x → φ x = 0) : HasCompactSupport (fibreFun φ k) := by
  have _ := hφ
  set s : ℝ := Real.sqrt (max ε 0) / 2 with hs
  refine HasCompactSupport.intro (isCompact_Icc (a := -s) (b := s)) fun t ht => ?_
  apply fibreFun_eq_zero φ k hφε
  have hst : s < |t| := by
    by_contra hcon
    exact ht (abs_le.mp (not_lt.mp hcon))
  have hs0 : 0 ≤ s := by positivity
  have h4 : 4 * s ^ 2 = max ε 0 := by
    rw [hs, div_pow, Real.sq_sqrt (le_max_right _ _)]; ring
  have ht2 : s ^ 2 < t ^ 2 := by
    have := abs_nonneg t
    calc s ^ 2 < |t| ^ 2 := by gcongr
      _ = t ^ 2 := sq_abs t
  have hsinh : t ^ 2 ≤ Real.sinh t ^ 2 := by
    have h1 : |t| ≤ |Real.sinh t| := by
      rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg t)
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ |Real.sinh t| ^ 2 := by gcongr
      _ = Real.sinh t ^ 2 := sq_abs _
  have hmax : ε ≤ max ε 0 := le_max_left _ _
  nlinarith

private theorem re_fibreIntegrand_ge (φ : ℝ → ℝ) (m : ℕ) (hφ0 : ∀ x, 0 ≤ φ x) {ε : ℝ}
    (hε : ε ≤ (1 / (2 ^ (m + 1 + 1) * (m + 1 : ℕ))) ^ 2) (hφε : ∀ x, ε ≤ x → φ x = 0) (t v : ℝ) :
    (7 / 8 : ℝ) * (2 * Real.cosh t) ^ (m + 1) * φ (4 * Real.sinh t ^ 2 + v ^ 2) ≤
      (fibreIntegrand φ (m + 1) t v).re := by
  by_cases hwin : ε ≤ 4 * Real.sinh t ^ 2 + v ^ 2
  · rw [fibreIntegrand_eq_zero φ (m + 1) hφε hwin, Complex.zero_re, hφε _ hwin, mul_zero]
  · rw [not_le] at hwin
    have ha : 0 < 2 * Real.cosh t := by positivity

    have hX : (0 : ℝ) < 2 ^ (m + 1 + 1) * (m + 1 : ℕ) := by positivity
    have hv2 : v ^ 2 ≤ (1 / (2 ^ (m + 1 + 1) * (m + 1 : ℕ))) ^ 2 := by
      have hsinh : 0 ≤ 4 * Real.sinh t ^ 2 := by positivity
      linarith
    have hv : |v| ≤ 1 / (2 ^ (m + 1 + 1) * (m + 1 : ℕ)) := by
      have := Real.abs_le_sqrt hv2
      rwa [Real.sqrt_sq (by positivity)] at this
    have hrad : 1 / (2 ^ (m + 1 + 1) * (m + 1 : ℕ)) ≤ 2 * Real.cosh t / (2 ^ (m + 3) * (m + 1)) := by
      have hc : 1 ≤ Real.cosh t := Real.one_le_cosh t
      have h3 : (2 : ℝ) ^ (m + 3) = 2 ^ (m + 1 + 1) * 2 := by rw [pow_succ]
      have hX' : (0 : ℝ) < 2 ^ (m + 1 + 1) * ((m : ℝ) + 1) := by positivity
      rw [h3, div_le_div_iff₀ hX (by positivity)]
      push_cast
      nlinarith [mul_nonneg hX'.le (sub_nonneg.mpr hc), hX']
    have hre := re_pow_ge_of_abs_im_le (2 * Real.cosh t) v ha m (hv.trans hrad)
    have hφv : 0 ≤ φ (4 * Real.sinh t ^ 2 + v ^ 2) := hφ0 _
    rw [fibreIntegrand, Complex.re_ofReal_mul]
    calc (7 / 8 : ℝ) * (2 * Real.cosh t) ^ (m + 1) * φ (4 * Real.sinh t ^ 2 + v ^ 2)
        = φ (4 * Real.sinh t ^ 2 + v ^ 2) * ((7 / 8 : ℝ) * (2 * Real.cosh t) ^ (m + 1)) := by ring
      _ ≤ φ (4 * Real.sinh t ^ 2 + v ^ 2) * ((⟨2 * Real.cosh t, v⟩ : ℂ) ^ (m + 1)).re :=
          mul_le_mul_of_nonneg_left hre hφv

private theorem re_fibreFun_eq_integral (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℕ) {ε : ℝ}
    (hφε : ∀ x, ε ≤ x → φ x = 0) (t : ℝ) :
    (fibreFun φ k t).re = ∫ v : ℝ, (fibreIntegrand φ k t v).re := by
  rw [fibreFun_eq]
  have h := integral_re (integrable_fibreIntegrand φ hφ k hφε t)
  simp only [RCLike.re_to_complex] at h
  exact h.symm

private theorem re_fibreFun_nonneg (φ : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) {ε : ℝ}
    (hε : ε ≤ (1 / (2 ^ (k + 1) * k)) ^ 2) (hφε : ∀ x, ε ≤ x → φ x = 0) (t : ℝ) : 0 ≤ (fibreFun φ k t).re := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  rw [re_fibreFun_eq_integral φ hφ (m + 1) hφε t]
  refine integral_nonneg fun v => ?_
  have h := re_fibreIntegrand_ge φ m hφ0 (by exact_mod_cast hε) hφε t v
  have h0 : 0 ≤ (7 / 8 : ℝ) * (2 * Real.cosh t) ^ (m + 1) * φ (4 * Real.sinh t ^ 2 + v ^ 2) :=
    mul_nonneg (by positivity) (hφ0 _)
  exact h0.trans h

private theorem re_fibreFun_zero_pos (φ : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {ε : ℝ} (hε : ε ≤ (1 / (2 ^ (k + 1) * k)) ^ 2) (hφε : ∀ x, ε ≤ x → φ x = 0)
    (hφpos : ∃ η > 0, ∀ x, |x| < η → 0 < φ x) : 0 < (fibreFun φ k 0).re := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨η, hη, hpos⟩ := hφpos

  set g : ℝ → ℝ := fun v => φ (v ^ 2) with hg
  have hg_cont : Continuous g := hφ.comp (continuous_pow 2)
  have hg_nonneg : (0 : ℝ → ℝ) ≤ g := fun v => hφ0 _
  have hg_supp : HasCompactSupport g := by
    set s : ℝ := Real.sqrt (max ε 0) with hs
    refine HasCompactSupport.intro (isCompact_Icc (a := -s) (b := s)) fun v hv => ?_
    have hsv : s < |v| := by
      by_contra hcon
      exact hv (abs_le.mp (not_lt.mp hcon))
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hv2 : max ε 0 < v ^ 2 := by
      have h1 : s ^ 2 < |v| ^ 2 := by gcongr
      rw [hs, Real.sq_sqrt (le_max_right _ _), sq_abs] at h1
      exact h1
    exact hφε _ ((le_max_left _ _).trans hv2.le)
  have hg0 : g 0 ≠ 0 := by
    have : 0 < φ (0 ^ 2) := hpos _ (by simpa using hη)
    exact this.ne'
  have hint_g : 0 < ∫ v, g v :=
    hg_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hg_supp hg_nonneg hg0
  set c : ℝ := (7 / 8 : ℝ) * (2 * Real.cosh 0) ^ (m + 1) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hpt : ∀ v : ℝ, c * g v ≤ (fibreIntegrand φ (m + 1) 0 v).re := by
    intro v
    have h := re_fibreIntegrand_ge φ m hφ0 (by exact_mod_cast hε) hφε 0 v
    have harg : 4 * Real.sinh 0 ^ 2 + v ^ 2 = v ^ 2 := by simp
    rw [harg] at h
    exact h
  have hint_re : Integrable fun v : ℝ => (fibreIntegrand φ (m + 1) 0 v).re :=
    (integrable_fibreIntegrand φ hφ (m + 1) hφε 0).re
  have hint_cg : Integrable fun v : ℝ => c * g v :=
    (hg_cont.integrable_of_hasCompactSupport hg_supp).const_mul c
  rw [re_fibreFun_eq_integral φ hφ (m + 1) hφε 0]
  calc (0 : ℝ) < c * ∫ v, g v := mul_pos hc0 hint_g
    _ = ∫ v, c * g v := (integral_const_mul c g).symm
    _ ≤ ∫ v, (fibreIntegrand φ (m + 1) 0 v).re := integral_mono hint_cg hint_re hpt

private def coefOfSq {P : Type} (c : ℝ × P → ℂ) (k : ℕ) : ℝ × P → ℂ :=
  fun q => if 0 < q.1 then c (Real.sqrt q.1, q.2) / ((Real.sqrt q.1 : ℂ) ^ k) else 0

private theorem contDiff_coefOfSq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (c : ℝ × P → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (k : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) (hc0 : ∀ r p, r ≤ r₀ → c (r, p) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (coefOfSq c k) := by
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  by_cases hd : 0 < q.1
  · have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × P => Real.sqrt q.1) q :=
      (Real.contDiffAt_sqrt hd.ne').comp q contDiffAt_fst
    have hc' : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × P => c (Real.sqrt q.1, q.2)) q :=
      hc.contDiffAt.comp q (hsq.prodMk contDiffAt_snd)
    have hre : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ((Real.sqrt q.1 : ℝ) : ℂ)) q :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp q hsq
    have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × P => (((Real.sqrt q.1 : ℝ) : ℂ) ^ k)⁻¹) q :=
      (hre.pow k).inv (pow_ne_zero k (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hd).ne'))
    refine (hc'.mul hinv).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds hd) fun q' hq' => ?_
    have h0 : (0 : ℝ) < q'.1 := hq'
    simp only [coefOfSq, if_pos h0, div_eq_mul_inv]
  · refine (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × P => (0 : ℂ)) q).congr_of_eventuallyEq ?_
    have hq : q ∈ {q : ℝ × P | q.1 < r₀ ^ 2} := lt_of_le_of_lt (not_lt.1 hd) (pow_pos hr₀ 2)
    refine Filter.eventuallyEq_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds hq) fun q' hq' => ?_
    have hlt : q'.1 < r₀ ^ 2 := hq'
    have hle : Real.sqrt q'.1 ≤ r₀ := (Real.sqrt_le_sqrt hlt.le).trans_eq (Real.sqrt_sq hr₀.le)
    simp only [coefOfSq]
    by_cases h0 : 0 < q'.1
    · rw [if_pos h0, hc0 _ _ hle, zero_div]
    · rw [if_neg h0]

private theorem hasCompactSupport_coefOfSq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (c : ℝ × P → ℂ)
    (hcc : HasCompactSupport c) (k : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) (hc0 : ∀ r p, r ≤ r₀ → c (r, p) = 0) :
    HasCompactSupport (coefOfSq c k) := by
  have _ := hr₀
  have _ := hc0
  refine HasCompactSupport.intro (hcc.isCompact.image ((continuous_fst.pow 2).prodMk continuous_snd)) fun q hq => ?_
  by_contra hne
  simp only [coefOfSq] at hne
  by_cases h0 : 0 < q.1
  · rw [if_pos h0] at hne
    have hc' : c (Real.sqrt q.1, q.2) ≠ 0 := fun h => hne (by rw [h, zero_div])
    exact hq ⟨(Real.sqrt q.1, q.2), subset_tsupport c (Function.mem_support.2 hc'), Prod.ext (Real.sq_sqrt h0.le) rfl⟩
  · rw [if_neg h0] at hne
    exact hne rfl

private theorem coefOfSq_sq {P : Type} (c : ℝ × P → ℂ) (k : ℕ) {r : ℝ} (hr : 0 < r) (p : P) :
    coefOfSq c k (r ^ 2, p) = c (r, p) / (r : ℂ) ^ k := by
  simp only [coefOfSq, if_pos (pow_pos hr 2), Real.sqrt_sq hr.le]

private lemma norm_coords_le_of_ne_zero {H : ℝ × ℝ → ℂ} {R : ℝ} (hR : ∀ x ∈ tsupport H, ‖x‖ ≤ R) {a b : ℝ}
    (h : H (a, b) ≠ 0) : ‖a‖ ≤ R ∧ ‖b‖ ≤ R := by
  have hn : ‖((a, b) : ℝ × ℝ)‖ ≤ R := hR _ (subset_tsupport H (Function.mem_support.mpr h))
  exact ⟨(norm_fst_le ((a, b) : ℝ × ℝ)).trans hn, (norm_snd_le ((a, b) : ℝ × ℝ)).trans hn⟩

private theorem intervalIntegrable_mul_U_of_bound (A : ℝ → ℂ) (K : ℝ) (hA : ContinuousOn A (Set.Ioo 0 Real.pi))
    (hAb : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ‖A θ‖ ≤ K) (n : ℤ) :
    IntervalIntegrable (fun θ => A θ * (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi := by

  have hAi : IntervalIntegrable A volume 0 Real.pi := by
    have hIoo : IntegrableOn A (Set.Ioo 0 Real.pi) volume :=
      ⟨hA.aestronglyMeasurable measurableSet_Ioo,
        HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioo_lt_top
          ((ae_restrict_mem measurableSet_Ioo).mono hAb)⟩
    rw [intervalIntegrable_iff, Set.uIoc_of_le Real.pi_pos.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).mpr hIoo

  have hU : Continuous fun θ : ℝ => (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((Chebyshev.U ℝ n).continuous.comp Real.continuous_cos)
  exact hAi.mul_continuousOn hU.continuousOn

private theorem integrable_torus (H : ℝ × ℝ → ℂ) (hH : Continuous H) (hHc : HasCompactSupport H) (w : ℝ → ℂ)
    (hw : Continuous w) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable fun t : ℝ =>
      w t * (H (r * Real.exp t, r * Real.exp (-t)) + c * H (-(r * Real.exp t), -(r * Real.exp (-t)))) := by
  obtain ⟨R, hR⟩ := hHc.isCompact.isBounded.exists_norm_le
  have hcont : Continuous fun t : ℝ =>
      w t * (H (r * Real.exp t, r * Real.exp (-t)) + c * H (-(r * Real.exp t), -(r * Real.exp (-t)))) := by
    fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_

  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (-(R / r)) (R / r))) ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hne : H (r * Real.exp t, r * Real.exp (-t)) + c * H (-(r * Real.exp t), -(r * Real.exp (-t))) ≠ 0 :=
    right_ne_zero_of_mul ht
  have hb : ‖r * Real.exp t‖ ≤ R ∧ ‖r * Real.exp (-t)‖ ≤ R := by
    by_cases h₁ : H (r * Real.exp t, r * Real.exp (-t)) = 0
    · have h₂ : H (-(r * Real.exp t), -(r * Real.exp (-t))) ≠ 0 := fun h₂ => hne (by rw [h₁, h₂, mul_zero, add_zero])
      obtain ⟨ha, hb⟩ := norm_coords_le_of_ne_zero hR h₂
      rw [norm_neg] at ha hb
      exact ⟨ha, hb⟩
    · exact norm_coords_le_of_ne_zero hR h₁
  obtain ⟨ha, hb⟩ := hb
  have hp₁ : 0 < r * Real.exp t := by positivity
  have hp₂ : 0 < r * Real.exp (-t) := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hp₁] at ha
  rw [Real.norm_eq_abs, abs_of_pos hp₂] at hb
  have h₁ : Real.exp t ≤ R / r := by
    rw [le_div_iff₀ hr, mul_comm]
    exact ha
  have h₂ : Real.exp (-t) ≤ R / r := by
    rw [le_div_iff₀ hr, mul_comm]
    exact hb
  have e₁ := Real.add_one_le_exp t
  have e₂ := Real.add_one_le_exp (-t)
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

private theorem pairing_layers_integrable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) (p : P) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ => ellipticTransform (entrySlice Φ p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi ∧
      Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
  constructor
  ·
    obtain ⟨hcont, hbound⟩ :=
      ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin P Φ hΦ.continuous hΦc hΦinv
    obtain ⟨K, hK⟩ := hbound {r} isCompact_singleton (Set.singleton_subset_iff.mpr hr)
    have hι : Continuous fun θ : ℝ => ((r, θ, p) : ℝ × ℝ × P) :=
      continuous_const.prodMk (continuous_id.prodMk continuous_const)
    have hA : ContinuousOn (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ) (Set.Ioo 0 Real.pi) :=
      hcont.comp hι.continuousOn fun θ hθ => ⟨hr, hθ.1, hθ.2⟩
    refine intervalIntegrable_mul_U_of_bound _ |K| hA (fun θ hθ => ?_) ((j : ℤ) - 2)
    exact (hK r (Set.mem_singleton r) θ hθ p).trans ((mul_le_mul_of_nonneg_right (le_abs_self K)
      (abs_nonneg _)).trans (mul_le_of_le_one_right (abs_nonneg K) (Real.abs_sin_le_one θ)))
  ·
    obtain ⟨h1, h2, -, -⟩ := contDiff_splitTransform_entrySlice P Φ hΦ hΦc hΦinv
    have hι : Continuous fun a : ℝ × ℝ => ((a.1, a.2, p) : ℝ × ℝ × P) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    have hSc : Continuous fun a : ℝ × ℝ => splitTransform (entrySlice Φ p) a.1 a.2 := h1.continuous.comp hι
    have hSs : HasCompactSupport fun a : ℝ × ℝ => splitTransform (entrySlice Φ p) a.1 a.2 := by
      refine HasCompactSupport.of_support_subset_isCompact
        (h2.isCompact.image (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) fun a ha => ?_
      exact ⟨(a.1, a.2, p), subset_tsupport _ ha, rfl⟩
    have hw : Continuous fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)
    exact integrable_torus (fun a : ℝ × ℝ => splitTransform (entrySlice Φ p) a.1 a.2) hSc hSs _ hw
      ((-1 : ℂ) ^ j) hr

private def pairingE {P : Type} (j : ℕ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r : ℝ) : ℂ :=
  discreteSeriesPairing j (splitTransform (entrySlice Φ p)) (ellipticTransform (entrySlice Φ p)) r

private def kappa : ℝ :=
  Classical.choose exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight

private theorem kappa_spec :
    0 < kappa ∧ ∀ (m : ℕ) (f : GL (Fin 2) ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g) →
      ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ r : ℝ, 0 < r →
        (∫ θ in (0 : ℝ)..Real.pi,
            ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          -(kappa : ℂ) * (1 / r : ℂ) *
            ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
              (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
                (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))) :=
  Classical.choose_spec exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight

private def entryFun (φs : ℕ → ℝ → ℝ) (j k : ℕ) : ℂ :=
  -2 * ((kappa : ℂ) * (∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) * fibreFun (φs k) k t) +
    2 * Real.pi * ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) * fibreFun (φs k) k t)

private def padMatrix (N : ℕ) (e : ℕ → ℕ → ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => if 2 ≤ (j : ℕ) ∧ (j : ℕ) ≤ k ∧ Even ((j : ℕ) + k) then e j k else if j = k then 1 else 0

private theorem padMatrix_blockTriangular (N : ℕ) (e : ℕ → ℕ → ℂ) : (padMatrix N e).BlockTriangular id := by
  intro j k hjk
  have hkj : (k : ℕ) < (j : ℕ) := hjk
  have h1 : ¬ (2 ≤ (j : ℕ) ∧ (j : ℕ) ≤ k ∧ Even ((j : ℕ) + k)) := fun h => absurd h.2.1 (not_le.mpr hkj)
  have h2 : j ≠ k := fun h => by
    subst h
    exact lt_irrefl _ hkj
  simp only [padMatrix]
  rw [if_neg h1, if_neg h2]

private theorem padMatrix_diag (N : ℕ) (e : ℕ → ℕ → ℂ) (k : Fin (N + 1)) :
    padMatrix N e k k = if 2 ≤ (k : ℕ) then e k k else 1 := by
  unfold padMatrix
  by_cases h : 2 ≤ (k : ℕ)
  · have hc : 2 ≤ (k : ℕ) ∧ (k : ℕ) ≤ k ∧ Even ((k : ℕ) + k) := ⟨h, le_rfl, ⟨(k : ℕ), rfl⟩⟩
    rw [if_pos hc, if_pos h]
  · have hc : ¬ (2 ≤ (k : ℕ) ∧ (k : ℕ) ≤ k ∧ Even ((k : ℕ) + k)) := fun hc => h hc.1
    rw [if_neg hc, if_pos rfl, if_neg h]

private theorem isUnit_det_padMatrix (N : ℕ) (e : ℕ → ℕ → ℂ) (he : ∀ k : ℕ, 2 ≤ k → k ≤ N → e k k ≠ 0) :
    IsUnit (padMatrix N e).det := by
  rw [Matrix.det_of_upperTriangular (padMatrix_blockTriangular N e), isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro k _
  rw [padMatrix_diag]
  split_ifs with hk
  · exact he k hk (Nat.lt_succ_iff.mp k.isLt)
  · exact one_ne_zero

open scoped Matrix in

private theorem padMatrix_mulVec_inv (N : ℕ) (e : ℕ → ℕ → ℂ) (he : ∀ k : ℕ, 2 ≤ k → k ≤ N → e k k ≠ 0)
    (c : Fin (N + 1) → ℂ) (j : Fin (N + 1)) :
    ∑ k : Fin (N + 1), padMatrix N e j k * ((padMatrix N e)⁻¹ *ᵥ c) k = c j := by
  have hinv : padMatrix N e *ᵥ ((padMatrix N e)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_padMatrix N e he), Matrix.one_mulVec]
  exact congrFun hinv j

open scoped Matrix in

private theorem inv_mulVec_eq_zero_of_lt_two (N : ℕ) (e : ℕ → ℕ → ℂ) (he : ∀ k : ℕ, 2 ≤ k → k ≤ N → e k k ≠ 0)
    (c : Fin (N + 1) → ℂ) (hc : ∀ j : Fin (N + 1), (j : ℕ) < 2 → c j = 0) (k : Fin (N + 1))
    (hk : (k : ℕ) < 2) :
    ((padMatrix N e)⁻¹ *ᵥ c) k = 0 := by
  have h1 := padMatrix_mulVec_inv N e he c k
  have hrow : ∀ i : Fin (N + 1), padMatrix N e k i = if k = i then 1 else 0 := by
    intro i
    simp only [padMatrix]
    rw [if_neg (fun h => absurd h.1 (not_le.mpr hk))]
  rw [hc k hk] at h1
  simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  exact h1

private theorem pairingE_member {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ}
    (hP : ∀ k, Profiles ψ (φs k) δ Δ (εs k)) (N : ℕ) (j k : Fin (N + 1)) (hj : 2 ≤ (j : ℕ))
    (p : Unit) {r : ℝ} (hr : 0 < r) :
    pairingE j (unitFamily (memberE ψ (φs k) k)) p r =
      (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k : ℕ) * padMatrix N (entryFun φs) j k := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (unitFamily (memberE ψ (φs k) k)) := contDiff_unitFamily (contDiff_memberE (hP k) k)
  have hΦc : HasCompactSupport (unitFamily (memberE ψ (φs k) k)) :=
    hasCompactSupport_unitFamily (hasCompactSupport_memberE (hP k) k)
  have hΦU : tsupport (unitFamily (memberE ψ (φs k) k)) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} :=
    tsupport_unitFamily (tsupport_memberE (hP k) k)
  unfold pairingE padMatrix
  by_cases hA : (j : ℕ) ≤ k ∧ Even ((j : ℕ) + k)
  ·
    rw [if_pos ⟨hj, hA.1, hA.2⟩]
    have hsurv := kappa_spec.2 (k : ℕ) (entrySlice (unitFamily (memberE ψ (φs k) k)) p)
      (continuous_entrySlice _ hΦ.continuous p) (hasCompactSupport_entrySlice _ hΦc hΦU p)
      (member_type ψ (φs k) k p)
    rw [pairing_member ψ (φs k) k p kappa hsurv hj (hA.1.trans (Nat.le_succ _)) hA.2 hr]
    simp only [entryFun]
    ring
  ·
    have hne : j ≠ k := by
      rintro rfl
      exact hA ⟨le_rfl, ⟨(j : ℕ), (two_mul _).symm.trans (by ring)⟩⟩
    rw [if_neg (fun h => hA ⟨h.2.1, h.2.2⟩), if_neg hne, mul_zero]
    have hU3 := discreteSeriesPairing_entrySlice_eq_zero_of_weight Unit (k : ℕ) (unitFamily (memberE ψ (φs k) k))
      hΦ hΦc hΦU (member_type ψ (φs k) k) p
    by_cases hpar : Even ((j : ℕ) + k)
    · have hlt : (k : ℕ) < j := lt_of_not_ge fun h => hA ⟨h, hpar⟩
      have hne1 : (j : ℕ) ≠ k + 1 := by
        intro h
        rw [h] at hpar
        exact (Nat.not_even_iff_odd.mpr ⟨k, by ring⟩) hpar
      exact hU3.1 j (by omega) r hr
    · exact hU3.2 j hj (fun h => hpar (even_iff_two_dvd.mpr h)) r hr

private theorem pairingE_eq {P : Type} (j : ℕ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r : ℝ) :
    pairingE j Φ p r =
      (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice Φ p) r θ *
          (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) -
        (2 * Real.pi / r : ℂ) *
          ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
            (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
              (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) :=
  rfl

private theorem torus_mul (r t : ℝ) : r * Real.exp t * (r * Real.exp (-t)) = r ^ 2 := by
  rw [Real.exp_neg, mul_mul_mul_comm, mul_inv_cancel₀ (Real.exp_pos t).ne', mul_one, sq]

private theorem torus_neg_mul (r t : ℝ) : -(r * Real.exp t) * -(r * Real.exp (-t)) = r ^ 2 := by
  rw [neg_mul_neg, torus_mul]

private theorem pairingE_detMul {P : Type} [NormedAddCommGroup P] (χ : ℝ → ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (j : ℕ) (p : P) {r : ℝ} (hr : 0 < r) :
    pairingE j (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p r = χ (r ^ 2) * pairingE j Φ p r := by
  have _ := hr
  rw [pairingE_eq, pairingE_eq]
  have hEpt : ∀ θ : ℝ,
      ellipticTransform (entrySlice (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) =
      χ (r ^ 2) * (ellipticTransform (entrySlice Φ p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := by
    intro θ
    rw [ellipticTransform_entrySlice_detMul, mul_assoc]
  have hHpt : ∀ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p) (r * Real.exp t)
          (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice (fun q => χ (Matrix.det (Matrix.of q.1)) * Φ q) p)
          (-(r * Real.exp t)) (-(r * Real.exp (-t)))) =
      χ (r ^ 2) * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) := by
    intro t
    rw [splitTransform_entrySlice_detMul, splitTransform_entrySlice_detMul, torus_mul, torus_neg_mul]
    ring
  simp only [hEpt, hHpt]
  have hE : (∫ θ in (0 : ℝ)..Real.pi, χ (r ^ 2) * (ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) =
      χ (r ^ 2) * ∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice Φ p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul _ _
  have hH : (∫ t : ℝ, χ (r ^ 2) * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))))) =
      χ (r ^ 2) * ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) :=
    integral_const_mul _ _
  rw [hE, hH]
  ring

private theorem pairingE_smul {P : Type} [NormedAddCommGroup P] (c : ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (j : ℕ) (p : P) (r : ℝ) : pairingE j (fun q => c * Φ q) p r = c * pairingE j Φ p r := by
  rw [pairingE_eq, pairingE_eq]
  have hs : ∀ a₁ a₂ : ℝ, splitTransform (entrySlice (fun q => c * Φ q) p) a₁ a₂ =
      c * splitTransform (entrySlice Φ p) a₁ a₂ :=
    fun a₁ a₂ => splitTransform_entrySlice_smul c Φ p a₁ a₂
  have he : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => c * Φ q) p) r θ =
      c * ellipticTransform (entrySlice Φ p) r θ :=
    fun θ => ellipticTransform_entrySlice_smul c Φ p r θ
  have hEpt : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => c * Φ q) p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) =
      c * (ellipticTransform (entrySlice Φ p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := by
    intro θ
    rw [he, mul_assoc]
  have hHpt : ∀ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (fun q => c * Φ q) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j *
          splitTransform (entrySlice (fun q => c * Φ q) p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) =
      c * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) := by
    intro t
    rw [hs, hs]
    ring
  simp only [hEpt, hHpt]
  have hE : (∫ θ in (0 : ℝ)..Real.pi, c * (ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) =
      c * ∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice Φ p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul _ _
  have hH : (∫ t : ℝ, c * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))))) =
      c * ∫ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) :=
    integral_const_mul _ _
  rw [hE, hH]
  ring

private theorem pairingE_add {P : Type} [NormedAddCommGroup P] (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (j : ℕ) (p : P) (r : ℝ)
    (hEΦ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hEΨ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Ψ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hHΦ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))))
    (hHΨ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Ψ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Ψ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) :
    pairingE j (fun q => Φ q + Ψ q) p r = pairingE j Φ p r + pairingE j Ψ p r := by
  rw [pairingE_eq, pairingE_eq, pairingE_eq]
  have hs : ∀ a₁ a₂ : ℝ, splitTransform (entrySlice (fun q => Φ q + Ψ q) p) a₁ a₂ =
      splitTransform (entrySlice Φ p) a₁ a₂ + splitTransform (entrySlice Ψ p) a₁ a₂ :=
    fun a₁ a₂ => splitTransform_entrySlice_add Φ Ψ hΦ hΦc hΨ hΨc p a₁ a₂
  have he : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => Φ q + Ψ q) p) r θ =
      ellipticTransform (entrySlice Φ p) r θ + ellipticTransform (entrySlice Ψ p) r θ :=
    fun θ => ellipticTransform_entrySlice_add Φ Ψ hΦ hΦc hΨ hΨc p r θ
  have hEpt : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => Φ q + Ψ q) p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) =
      ellipticTransform (entrySlice Φ p) r θ * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) +
        ellipticTransform (entrySlice Ψ p) r θ *
          (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
    intro θ
    rw [he, add_mul]
  have hHpt : ∀ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (fun q => Φ q + Ψ q) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j *
          splitTransform (entrySlice (fun q => Φ q + Ψ q) p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) =
      (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
          (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
            (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) +
        (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
          (splitTransform (entrySlice Ψ p) (r * Real.exp t) (r * Real.exp (-t)) +
            (-1 : ℂ) ^ j * splitTransform (entrySlice Ψ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
    intro t
    rw [hs, hs]
    ring
  simp only [hEpt, hHpt]
  rw [intervalIntegral.integral_add hEΦ hEΨ, integral_add hHΦ hHΨ]
  ring

private theorem pairingE_sub {P : Type} [NormedAddCommGroup P] (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (j : ℕ) (p : P) (r : ℝ)
    (hEΦ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hEΨ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Ψ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hHΦ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))))
    (hHΨ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Ψ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Ψ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) :
    pairingE j (fun q => Φ q - Ψ q) p r = pairingE j Φ p r - pairingE j Ψ p r := by

  have hΨ' : Continuous fun q : (Fin 2 → Fin 2 → ℝ) × P => (-1 : ℂ) * Ψ q := continuous_const.mul hΨ
  have hΨ'c : HasCompactSupport fun q : (Fin 2 → Fin 2 → ℝ) × P => (-1 : ℂ) * Ψ q :=
    hΨc.mul_left (f := fun _ => (-1 : ℂ))
  have hfun : (fun q : (Fin 2 → Fin 2 → ℝ) × P => Φ q - Ψ q) = fun q => Φ q + (-1 : ℂ) * Ψ q := by
    funext q
    ring
  have he : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) r θ =
      (-1 : ℂ) * ellipticTransform (entrySlice Ψ p) r θ :=
    fun θ => ellipticTransform_entrySlice_smul (-1) Ψ p r θ
  have hs : ∀ a₁ a₂ : ℝ, splitTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) a₁ a₂ =
      (-1 : ℂ) * splitTransform (entrySlice Ψ p) a₁ a₂ :=
    fun a₁ a₂ => splitTransform_entrySlice_smul (-1) Ψ p a₁ a₂
  have hEΨ' : IntervalIntegrable (fun θ => ellipticTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi := by
    have hfe : (fun θ => ellipticTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        fun θ => (-1 : ℂ) * (ellipticTransform (entrySlice Ψ p) r θ *
          (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := by
      funext θ
      rw [he, mul_assoc]
    rw [hfe]
    exact hEΨ.const_mul (-1 : ℂ)
  have hHΨ' : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j *
          splitTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
    have hfh : (fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j *
            splitTransform (entrySlice (fun q => (-1 : ℂ) * Ψ q) p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) =
        fun t : ℝ => (-1 : ℂ) * ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
          (splitTransform (entrySlice Ψ p) (r * Real.exp t) (r * Real.exp (-t)) +
            (-1 : ℂ) ^ j * splitTransform (entrySlice Ψ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) := by
      funext t
      rw [hs, hs]
      ring
    rw [hfh]
    exact hHΨ.const_mul (-1 : ℂ)
  rw [hfun, pairingE_add Φ (fun q => (-1 : ℂ) * Ψ q) hΦ hΦc hΨ' hΨ'c j p r hEΦ hEΨ' hHΦ hHΨ', pairingE_smul]
  ring

private theorem pairingE_sum {P : Type} [NormedAddCommGroup P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ∀ i ∈ s, Continuous (Φ i))
    (hΦc : ∀ i ∈ s, HasCompactSupport (Φ i)) (j : ℕ) (p : P) (r : ℝ)
    (hE : ∀ i ∈ s, IntervalIntegrable (fun θ => ellipticTransform (entrySlice (Φ i) p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hH : ∀ i ∈ s, Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (Φ i) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice (Φ i) p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) :
    pairingE j (fun q => ∑ i ∈ s, Φ i q) p r = ∑ i ∈ s, pairingE j (Φ i) p r := by
  have hfn : (fun q : (Fin 2 → Fin 2 → ℝ) × P => ∑ i ∈ s, Φ i q) = ∑ i ∈ s, Φ i := by
    funext q
    exact (Finset.sum_apply q s Φ).symm
  have hs : ∀ a₁ a₂ : ℝ, splitTransform (entrySlice (fun q => ∑ i ∈ s, Φ i q) p) a₁ a₂ =
      ∑ i ∈ s, splitTransform (entrySlice (Φ i) p) a₁ a₂ := by
    intro a₁ a₂
    rw [hfn]
    exact splitTransform_entrySlice_sum s Φ hΦ hΦc p a₁ a₂
  have he : ∀ θ : ℝ, ellipticTransform (entrySlice (fun q => ∑ i ∈ s, Φ i q) p) r θ =
      ∑ i ∈ s, ellipticTransform (entrySlice (Φ i) p) r θ := by
    intro θ
    rw [hfn]
    exact ellipticTransform_entrySlice_sum s Φ hΦ hΦc p r θ
  have hHpt : ∀ t : ℝ, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      ((∑ i ∈ s, splitTransform (entrySlice (Φ i) p) (r * Real.exp t) (r * Real.exp (-t))) +
        (-1 : ℂ) ^ j * ∑ i ∈ s, splitTransform (entrySlice (Φ i) p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) =
      ∑ i ∈ s, (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
        (splitTransform (entrySlice (Φ i) p) (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform (entrySlice (Φ i) p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
    intro t
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [pairingE_eq, hs, he, Finset.sum_mul, hHpt]
  rw [intervalIntegral.integral_finsetSum hE, integral_finsetSum s hH, Finset.mul_sum, ← Finset.sum_sub_distrib]

private theorem pairingE_add_pi {P : Type} [NormedAddCommGroup P] (Φ Ψ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (j : ℕ) (p : P) (r : ℝ)
    (hEΦ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hEΨ : IntervalIntegrable (fun θ => ellipticTransform (entrySlice Ψ p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hHΦ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))))
    (hHΨ : Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice Ψ p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice Ψ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) :
    pairingE j (Φ + Ψ) p r = pairingE j Φ p r + pairingE j Ψ p r := by
  show pairingE j (fun q => Φ q + Ψ q) p r = pairingE j Φ p r + pairingE j Ψ p r
  exact pairingE_add Φ Ψ hΦ hΦc hΨ hΨc j p r hEΦ hEΨ hHΦ hHΨ

private theorem pairingE_sum_pi {P : Type} [NormedAddCommGroup P] {ι : Type} (s : Finset ι)
    (Φ : ι → (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ∀ i ∈ s, Continuous (Φ i))
    (hΦc : ∀ i ∈ s, HasCompactSupport (Φ i)) (j : ℕ) (p : P) (r : ℝ)
    (hE : ∀ i ∈ s, IntervalIntegrable (fun θ => ellipticTransform (entrySlice (Φ i) p) r θ *
      (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi)
    (hH : ∀ i ∈ s, Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
      (splitTransform (entrySlice (Φ i) p) (r * Real.exp t) (r * Real.exp (-t)) +
        (-1 : ℂ) ^ j * splitTransform (entrySlice (Φ i) p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) :
    pairingE j (∑ i ∈ s, Φ i) p r = ∑ i ∈ s, pairingE j (Φ i) p r := by
  have hfn : (∑ i ∈ s, Φ i) = fun q : (Fin 2 → Fin 2 → ℝ) × P => ∑ i ∈ s, Φ i q := by
    funext q
    exact Finset.sum_apply q s Φ
  rw [hfn]
  exact pairingE_sum s Φ hΦ hΦc j p r hE hH

private theorem pairingE_memberCorr_eq_zero {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) {j : ℕ}
    (hj : 2 ≤ j) (p : Unit) {r : ℝ} (hr : 0 < r) : pairingE j (memberCorr ψ φ k) p r = 0 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := memberCorr_props hP k
  have hU3 := discreteSeriesPairing_entrySlice_eq_zero_of_weight Unit (k % 2) (memberCorr ψ φ k) h1 h2 h3 h4 p
  unfold pairingE
  by_cases hle : k % 2 + 2 ≤ j
  · exact hU3.1 j hle r hr
  · exact hU3.2 j hj (by omega) r hr

private theorem pairingE_unitFamily_memberE_eq_zero {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) {j k : ℕ}
    (hkj : k < j) (hj : 2 ≤ j) (p : Unit) {r : ℝ} (hr : 0 < r) :
    pairingE j (unitFamily (memberE ψ φ k)) p r = 0 := by
  have hU3 := discreteSeriesPairing_entrySlice_eq_zero_of_weight Unit k (unitFamily (memberE ψ φ k))
    (contDiff_unitFamily (contDiff_memberE hP k)) (hasCompactSupport_unitFamily (hasCompactSupport_memberE hP k))
    (tsupport_unitFamily (tsupport_memberE hP k)) (member_type ψ φ k) p
  unfold pairingE
  by_cases hpar : Even (j + k)
  · have hne : j ≠ k + 1 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ⟨k, by ring⟩) hpar
    exact hU3.1 j (by omega) r hr
  · exact hU3.2 j hj (fun h => hpar (even_iff_two_dvd.mpr h)) r hr

private theorem pairingE_adjuster_eq {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) (k : ℕ) {j : ℕ}
    (hj : 2 ≤ j) (p : Unit) {r : ℝ} (hr : 0 < r) :
    pairingE j (adjuster ψ φ k) p r = pairingE j (unitFamily (memberE ψ φ k)) p r := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (unitFamily (memberE ψ φ k)) := contDiff_unitFamily (contDiff_memberE hP k)
  have hΦc : HasCompactSupport (unitFamily (memberE ψ φ k)) :=
    hasCompactSupport_unitFamily (hasCompactSupport_memberE hP k)
  have hΦU : tsupport (unitFamily (memberE ψ φ k)) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} :=
    tsupport_unitFamily (tsupport_memberE hP k)
  obtain ⟨h1, h2, h3, -, -⟩ := memberCorr_props hP k
  obtain ⟨hEΦ, hHΦ⟩ := pairing_layers_integrable (unitFamily (memberE ψ φ k)) hΦ hΦc hΦU j p hr
  obtain ⟨hEΨ, hHΨ⟩ := pairing_layers_integrable (memberCorr ψ φ k) h1 h2 h3 j p hr
  have hsub := pairingE_sub (unitFamily (memberE ψ φ k)) (memberCorr ψ φ k) hΦ.continuous hΦc h1.continuous h2 j p r
    hEΦ hEΨ hHΦ hHΨ
  have hdef : pairingE j (adjuster ψ φ k) p r =
      pairingE j (fun q => unitFamily (memberE ψ φ k) q - memberCorr ψ φ k q) p r := rfl
  rw [hdef, hsub, pairingE_memberCorr_eq_zero hP k hj p hr, sub_zero]

private theorem pairingE_adjuster {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ}
    (hP : ∀ k, Profiles ψ (φs k) δ Δ (εs k)) (N : ℕ) (j k : Fin (N + 1)) (hj : 2 ≤ (j : ℕ)) (p : Unit) {r : ℝ}
    (hr : 0 < r) :
    pairingE j (adjuster ψ (φs k) k) p r = (ψ (r ^ 2) : ℂ) * (r : ℂ) ^ (k : ℕ) * padMatrix N (entryFun φs) j k := by
  rw [pairingE_adjuster_eq (hP k) k hj p hr, pairingE_member hP N j k hj p hr]

private theorem pairingE_adjuster_eq_zero {ψ φ : ℝ → ℝ} {δ Δ ε : ℝ} (hP : Profiles ψ φ δ Δ ε) {j k : ℕ}
    (hkj : k < j) (hj : 2 ≤ j) (p : Unit) {r : ℝ} (hr : 0 < r) : pairingE j (adjuster ψ φ k) p r = 0 := by
  rw [pairingE_adjuster_eq hP k hj p hr, pairingE_unitFamily_memberE_eq_zero hP hkj hj p hr]

private theorem det_ne_zero_of_mem_tsupport {P : Type} [TopologicalSpace P] {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ}
    (hsupp : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) {x : (Fin 2 → Fin 2 → ℝ) × P}
    (hx : x ∈ tsupport Φ) : Matrix.det (Matrix.of x.1) ≠ 0 :=
  isUnit_iff_ne_zero.mp (hsupp hx)

private theorem eq_zero_of_det_eq_zero {P : Type} [TopologicalSpace P] {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ}
    (hsupp : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (N : Fin 2 → Fin 2 → ℝ) (p : P)
    (hN : Matrix.det (Matrix.of N) = 0) : Φ (N, p) = 0 := by
  by_contra hne
  exact det_ne_zero_of_mem_tsupport hsupp (subset_tsupport Φ (Function.mem_support.mpr hne)) hN

private theorem apply_mul_coe_eq {P : Type} [TopologicalSpace P] (m : ℤ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hsupp : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (htype : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice Φ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ m k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ m k₂ : ℂˣ) : ℂ) * entrySlice Φ p g)
    (k : rowIsometrySubgroup₀ ℝ) (M : Fin 2 → Fin 2 → ℝ) (p : P) :
    Φ (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) =
        ((archWeightCharℝ m k : ℂˣ) : ℂ) * Φ (M, p) ∧
      Φ (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M), p) =
        ((archWeightCharℝ m k : ℂˣ) : ℂ) * Φ (M, p) := by
  by_cases hdet : Matrix.det (Matrix.of M) = 0
  ·
    have h0 : Φ (M, p) = 0 := eq_zero_of_det_eq_zero hsupp M p hdet
    have h1 : Φ (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) = 0 :=
      eq_zero_of_det_eq_zero hsupp _ p (by rw [Equiv.apply_symm_apply, Matrix.det_mul, hdet, zero_mul])
    have h2 : Φ (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M), p) = 0 :=
      eq_zero_of_det_eq_zero hsupp _ p (by rw [Equiv.apply_symm_apply, Matrix.det_mul, hdet, mul_zero])
    rw [h0, h1, h2, mul_zero]
    exact ⟨rfl, rfl⟩
  ·

    have hgM : ((Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of M) hdet : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of M := rfl
    constructor
    · have h := htype p 1 k (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of M) hdet)
      simp only [entrySlice, OneMemClass.coe_one, one_mul, Units.val_mul, hgM, _root_.map_one, Units.val_one,
        Equiv.symm_apply_apply] at h
      exact h
    · have h := htype p k 1 (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of M) hdet)
      simp only [entrySlice, OneMemClass.coe_one, mul_one, Units.val_mul, hgM, _root_.map_one, Units.val_one,
        Equiv.symm_apply_apply] at h
      exact h

private theorem finiteDimensional_span_range_of_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (T : ι → V) (S : Finset V) (h : ∀ i, T i ∈ Submodule.span ℂ (S : Set V)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range T)) := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (S : Set V)) := FiniteDimensional.span_of_finite ℂ S.finite_toSet
  exact Submodule.finiteDimensional_of_le (Submodule.span_le.mpr (Set.range_subset_iff.mpr h))

private lemma re_integral {f : ℝ → ℂ} (hf : Integrable f) : (∫ t, f t).re = ∫ t, (f t).re := by
  have h := integral_re hf
  simpa using h.symm

private theorem re_kernel_integral_pos (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (hre : ∀ t, 0 ≤ (h t).re) (h0 : 0 < (h 0).re) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) (hk : 1 ≤ k) :
    0 < ((κ : ℂ) * (∫ t : ℝ, (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t) +
        2 * Real.pi * ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t).re := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

  have hcont₁ : Continuous fun t : ℝ => (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t :=
    (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp (continuous_const.mul continuous_abs))).mul hh
  have hsupp₁ : HasCompactSupport fun t : ℝ => (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t := hhc.mul_left
  have hint₁ : Integrable fun t : ℝ => (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t :=
    hcont₁.integrable_of_hasCompactSupport hsupp₁
  have hcont₂ : Continuous fun t : ℝ => (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)).mul hh
  have hsupp₂ : HasCompactSupport fun t : ℝ => (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t := hhc.mul_left
  have hint₂ : Integrable fun t : ℝ => (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t :=
    hcont₂.integrable_of_hasCompactSupport hsupp₂

  have hA : (∫ t : ℝ, (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t).re =
      ∫ t : ℝ, Real.sinh (((k : ℝ) - 1) * |t|) * (h t).re := by
    rw [re_integral hint₁]
    simp only [Complex.re_ofReal_mul]
  have hB : (∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t).re =
      ∫ t : ℝ, Real.exp (-(((k : ℝ) - 1) * |t|)) * (h t).re := by
    rw [re_integral hint₂]
    simp only [Complex.re_ofReal_mul]

  have hA₀ : 0 ≤ ∫ t : ℝ, Real.sinh (((k : ℝ) - 1) * |t|) * (h t).re :=
    integral_nonneg fun t => mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hk' (abs_nonneg t))) (hre t)

  have hgc : Continuous fun t : ℝ => Real.exp (-(((k : ℝ) - 1) * |t|)) * (h t).re :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg).mul (Complex.continuous_re.comp hh)
  have hgs : HasCompactSupport fun t : ℝ => Real.exp (-(((k : ℝ) - 1) * |t|)) * (h t).re :=
    (hhc.comp_left Complex.zero_re).mul_left
  have hg0 : (fun t : ℝ => Real.exp (-(((k : ℝ) - 1) * |t|)) * (h t).re) 0 ≠ 0 := by
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
    exact h0.ne'
  have hB₀ : 0 < ∫ t : ℝ, Real.exp (-(((k : ℝ) - 1) * |t|)) * (h t).re :=
    hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero hgs (fun t => mul_nonneg (Real.exp_pos _).le (hre t)) hg0

  have hsum : ((κ : ℂ) * (∫ t : ℝ, (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t) +
      2 * Real.pi * ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t).re =
        κ * (∫ t : ℝ, (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * h t).re +
          2 * Real.pi * (∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * h t).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hsum, hA, hB]
  have hπ := Real.pi_pos
  nlinarith [mul_nonneg hκ.le hA₀, mul_pos (mul_pos two_pos hπ) hB₀]

private theorem entryFun_diag_ne_zero (φs : ℕ → ℝ → ℝ) (εs : ℕ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hφ : Continuous (φs k)) (hφ0 : ∀ x, 0 ≤ φs k x) (hε : εs k ≤ (1 / (2 ^ (k + 1) * k)) ^ 2)
    (hφε : ∀ x, εs k ≤ x → φs k x = 0) (hφpos : ∃ η > 0, ∀ x, |x| < η → 0 < φs k x) :
    entryFun φs k k ≠ 0 := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hpos := re_kernel_integral_pos (fibreFun (φs k) k) (continuous_fibreFun (φs k) k hφ hφε)
    (hasCompactSupport_fibreFun (φs k) k hφ hφε) (re_fibreFun_nonneg (φs k) k hk1 hφ hφ0 hε hφε)
    (re_fibreFun_zero_pos (φs k) k hk1 hφ hφ0 hε hφε hφpos) kappa kappa_spec.1 k hk1
  intro h0
  unfold entryFun at h0
  have h2 : (kappa : ℂ) * (∫ t : ℝ, (Real.sinh (((k : ℝ) - 1) * |t|) : ℂ) * fibreFun (φs k) k t) +
      2 * Real.pi * ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * fibreFun (φs k) k t = 0 :=
    (mul_eq_zero.mp h0).resolve_left (by norm_num)
  rw [h2, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

private theorem exists_plateau (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ψ : ℝ → ℝ, ∃ δ Δ : ℝ, 0 < δ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x, x ≤ δ → ψ x = 0) ∧ (∀ x, Δ ≤ x → ψ x = 0) ∧
      ∀ x ∈ Set.Icc a b, ψ x = 1 := by
  let f : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 2 + a / 4
      rOut := (b - a) / 2 + a / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hrIn : f.rIn = (b - a) / 2 + a / 4 := rfl
  have hrOut : f.rOut = (b - a) / 2 + a / 2 := rfl
  refine ⟨f, a / 4, (a + b) / 2 + ((b - a) / 2 + a / 2), by linarith, f.contDiff, ?_, ?_, ?_⟩
  · intro x hx
    apply f.zero_of_le_dist
    rw [hrOut, Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  · intro x hx
    apply f.zero_of_le_dist
    rw [hrOut, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  · intro x hx
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, hrIn, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem exists_eccentricity (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, ε ≤ x → φ x = 0) ∧
      ∃ η > 0, ∀ x, |x| < η → 0 < φ x := by
  let g : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 2
      rOut := ε
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hrOut : g.rOut = ε := rfl
  refine ⟨g, g.contDiff, fun x => g.nonneg' x, ?_, ε, hε, ?_⟩
  · intro x hx
    apply g.zero_of_le_dist
    rw [hrOut, Real.dist_eq, sub_zero]
    exact hx.trans (le_abs_self x)
  · intro x hx
    apply g.pos_of_mem_ball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hrOut]
    exact hx

private theorem exists_gear (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ (ψ : ℝ → ℝ) (φs : ℕ → ℝ → ℝ) (δ Δ : ℝ) (εs : ℕ → ℝ), (∀ k, Profiles ψ (φs k) δ Δ (εs k)) ∧
      (∀ x ∈ Set.Icc a b, ψ x = 1) ∧ (∀ k x, 0 ≤ φs k x) ∧
      (∀ k : ℕ, 1 ≤ k → εs k ≤ (1 / (2 ^ (k + 1) * k)) ^ 2) ∧ ∀ k, ∃ η > 0, ∀ x, |x| < η → 0 < φs k x := by
  obtain ⟨ψ, δ, Δ, hδ, hψ, hψ0, hψΔ, hψ1⟩ := exists_plateau a b ha hab
  have hεpos : ∀ k : ℕ, (0 : ℝ) < (1 / (2 ^ (k + 1) * ((k : ℝ) + 1))) ^ 2 := fun k => by positivity
  choose φs hφ hφ0 hφε hφpos using fun k : ℕ => exists_eccentricity ((1 / (2 ^ (k + 1) * ((k : ℝ) + 1))) ^ 2)
    (hεpos k)
  refine ⟨ψ, φs, δ, Δ, fun k => (1 / (2 ^ (k + 1) * ((k : ℝ) + 1))) ^ 2,
    fun k => ⟨hδ, hψ, hψ0, hψΔ, hφ k, hεpos k, hφε k⟩, hψ1, hφ0, fun k hk => ?_, hφpos⟩

  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply pow_le_pow_left₀ (by positivity)
  exact one_div_le_one_div_of_le (mul_pos h2 hk0) (mul_le_mul_of_nonneg_left (by linarith) h2.le)

private theorem translate_mem_span {P : Type} {N : ℕ} (L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (X : Fin (N + 1) → ℝ × P → ℂ) (g J : Fin (N + 1) → (Fin 2 → Fin 2 → ℝ) → ℂ) (F : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hF : ∀ q : (Fin 2 → Fin 2 → ℝ) × P,
      F q = L₀ q + L₁ q + ∑ i : Fin (N + 1), X i (Matrix.det (Matrix.of q.1), q.2) * (g i q.1 - J i q.1))
    (S : Finset ((Fin 2 → Fin 2 → ℝ) × P → ℂ)) (hS₀ : L₀ ∈ S) (hS₁ : L₁ ∈ S)
    (hSg : ∀ i, (fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * g i q.1) ∈ S)
    (hSJ : ∀ i, (fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * J i q.1) ∈ S)
    (τ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ))
    (hτ : ∀ M, Matrix.det (Matrix.of (τ M)) = Matrix.det (Matrix.of M)) (c₀ c₁ : ℂ) (cg cJ : Fin (N + 1) → ℂ)
    (h₀ : ∀ M p, L₀ (τ M, p) = c₀ * L₀ (M, p)) (h₁ : ∀ M p, L₁ (τ M, p) = c₁ * L₁ (M, p))
    (hg : ∀ i M, g i (τ M) = cg i * g i M) (hJ : ∀ i M, J i (τ M) = cJ i * J i M) :
    (fun r : (Fin 2 → Fin 2 → ℝ) × P => F (τ r.1, r.2)) ∈
      Submodule.span ℂ (S : Set ((Fin 2 → Fin 2 → ℝ) × P → ℂ)) := by
  have hfun : (fun r : (Fin 2 → Fin 2 → ℝ) × P => F (τ r.1, r.2)) =
      c₀ • L₀ + c₁ • L₁ + ∑ i : Fin (N + 1),
        (cg i • (fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * g i q.1) -
          cJ i • fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * J i q.1) := by
    funext ⟨M, p⟩
    simp only [hF, hτ, h₀, h₁, hg, hJ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.sub_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hS₀))
      (Submodule.smul_mem _ _ (Submodule.subset_span hS₁)))
    (Submodule.sum_mem _ fun i _ => Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (hSg i)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hSJ i))))

private theorem finiteDimensional_span_translates {P : Type} (N : ℕ)
    (L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (m₀ m₁ : ℤ)
    (hL₀ : ∀ (k : rowIsometrySubgroup₀ ℝ) (M : Fin 2 → Fin 2 → ℝ) (p : P),
      L₀ (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) =
          ((archWeightCharℝ m₀ k : ℂˣ) : ℂ) * L₀ (M, p) ∧
        L₀ (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M), p) =
          ((archWeightCharℝ m₀ k : ℂˣ) : ℂ) * L₀ (M, p))
    (hL₁ : ∀ (k : rowIsometrySubgroup₀ ℝ) (M : Fin 2 → Fin 2 → ℝ) (p : P),
      L₁ (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) =
          ((archWeightCharℝ m₁ k : ℂˣ) : ℂ) * L₁ (M, p) ∧
        L₁ (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M), p) =
          ((archWeightCharℝ m₁ k : ℂˣ) : ℂ) * L₁ (M, p))
    (X : Fin (N + 1) → ℝ × P → ℂ) (g J : Fin (N + 1) → (Fin 2 → Fin 2 → ℝ) → ℂ) (mg mJ : Fin (N + 1) → ℤ)
    (hg : ∀ (i : Fin (N + 1)) (k : rowIsometrySubgroup₀ ℝ) (M : Fin 2 → Fin 2 → ℝ),
      g i (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
          ((archWeightCharℝ (mg i) k : ℂˣ) : ℂ) * g i M ∧
        g i (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M)) =
          ((archWeightCharℝ (mg i) k : ℂˣ) : ℂ) * g i M)
    (hJ : ∀ (i : Fin (N + 1)) (k : rowIsometrySubgroup₀ ℝ) (M : Fin 2 → Fin 2 → ℝ),
      J i (Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
          ((archWeightCharℝ (mJ i) k : ℂˣ) : ℂ) * J i M ∧
        J i (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M)) =
          ((archWeightCharℝ (mJ i) k : ℂˣ) : ℂ) * J i M)
    (F : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hF : ∀ q : (Fin 2 → Fin 2 → ℝ) × P,
      F q = L₀ q + L₁ q + ∑ i : Fin (N + 1), X i (Matrix.det (Matrix.of q.1), q.2) * (g i q.1 - J i q.1)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
      fun r : (Fin 2 → Fin 2 → ℝ) × P =>
        F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
      fun r : (Fin 2 → Fin 2 → ℝ) × P =>
        F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) := by
  classical
  have hdet : ∀ k : rowIsometrySubgroup₀ ℝ, Matrix.det ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    fun k => ((mem_rowIsometrySubgroup₀_iff ℝ).mp k.2).1
  obtain ⟨S, hS₀, hS₁, hSg, hSJ⟩ : ∃ S : Finset ((Fin 2 → Fin 2 → ℝ) × P → ℂ), L₀ ∈ S ∧ L₁ ∈ S ∧
      (∀ i, (fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * g i q.1) ∈ S) ∧
      ∀ i, (fun q : (Fin 2 → Fin 2 → ℝ) × P => X i (Matrix.det (Matrix.of q.1), q.2) * J i q.1) ∈ S :=
    ⟨{L₀, L₁} ∪
        Finset.univ.image (fun i : Fin (N + 1) => fun q : (Fin 2 → Fin 2 → ℝ) × P =>
          X i (Matrix.det (Matrix.of q.1), q.2) * g i q.1) ∪
        Finset.univ.image (fun i : Fin (N + 1) => fun q : (Fin 2 → Fin 2 → ℝ) × P =>
          X i (Matrix.det (Matrix.of q.1), q.2) * J i q.1),
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _)),
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))),
      fun i => Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
      fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  refine ⟨finiteDimensional_span_range_of_mem_span _ S fun k => ?_,
    finiteDimensional_span_range_of_mem_span _ S fun k => ?_⟩
  · exact translate_mem_span L₀ L₁ X g J F hF S hS₀ hS₁ hSg hSJ
      (fun M => Matrix.of.symm (Matrix.of M * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      (fun M => by simp only [Equiv.apply_symm_apply, Matrix.det_mul, hdet, mul_one])
      ((archWeightCharℝ m₀ k : ℂˣ) : ℂ) ((archWeightCharℝ m₁ k : ℂˣ) : ℂ)
      (fun i => ((archWeightCharℝ (mg i) k : ℂˣ) : ℂ)) (fun i => ((archWeightCharℝ (mJ i) k : ℂˣ) : ℂ))
      (fun M p => (hL₀ k M p).1) (fun M p => (hL₁ k M p).1) (fun i M => (hg i k M).1) (fun i M => (hJ i k M).1)
  · exact translate_mem_span L₀ L₁ X g J F hF S hS₀ hS₁ hSg hSJ
      (fun M => Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of M))
      (fun M => by simp only [Equiv.apply_symm_apply, Matrix.det_mul, hdet, one_mul])
      ((archWeightCharℝ m₀ k : ℂˣ) : ℂ) ((archWeightCharℝ m₁ k : ℂˣ) : ℂ)
      (fun i => ((archWeightCharℝ (mg i) k : ℂˣ) : ℂ)) (fun i => ((archWeightCharℝ (mJ i) k : ℂˣ) : ℂ))
      (fun M p => (hL₀ k M p).2) (fun M p => (hL₁ k M p).2) (fun i M => (hg i k M).2) (fun i M => (hJ i k M).2)

private theorem relation_coefOfSq {P : Type} {ι : Type} [Fintype ι] (α : ι → ℂ) (T : ι → ℝ × P → ℂ) (k : ℕ) {n : ℕ}
    (c : Fin n → ℂ) (q : Fin n → P) (hT : ∀ (i : ι) (r : ℝ), ∑ j, c j * T i (r, q j) = 0) (d : ℝ) :
    ∑ j, c j * coefOfSq (fun x => ∑ i, α i * T i x) k (d, q j) = 0 := by
  by_cases hd : 0 < d
  · simp only [coefOfSq, hd, if_true]
    have h1 : ∀ j, c j * ((∑ i, α i * T i (Real.sqrt d, q j)) / ((Real.sqrt d : ℂ) ^ k))
        = (∑ i, α i * (c j * T i (Real.sqrt d, q j))) / ((Real.sqrt d : ℂ) ^ k) := by
      intro j
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [h1, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hT, mul_zero, Finset.sum_const_zero, zero_div]
  · simp only [coefOfSq, hd, if_false, mul_zero, Finset.sum_const_zero]

private theorem relation_witness {P : Type} {N : ℕ} (F L : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (X : Fin (N + 1) → ℝ × P → ℂ)
    (gk Jk : Fin (N + 1) → (Fin 2 → Fin 2 → ℝ) → ℂ)
    (hF : ∀ r : (Fin 2 → Fin 2 → ℝ) × P,
      F r = L r + ∑ k, X k (Matrix.det (Matrix.of r.1), r.2) * (gk k r.1 - Jk k r.1))
    {n : ℕ} (c : Fin n → ℂ) (q : Fin n → P) (hL : ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * L (M, q j) = 0)
    (hX : ∀ (k : Fin (N + 1)) (d : ℝ), ∑ j, c j * X k (d, q j) = 0) (M : Fin 2 → Fin 2 → ℝ) :
    ∑ j, c j * F (M, q j) = 0 := by
  simp only [hF, mul_add, Finset.sum_add_distrib, hL, zero_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  calc ∑ j, c j * (X k (Matrix.det (Matrix.of M), q j) * (gk k M - Jk k M))
      = (∑ j, c j * X k (Matrix.det (Matrix.of M), q j)) * (gk k M - Jk k M) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [hX k, zero_mul]

private def targetVec {P : Type} (N : ℕ) (T : ℕ → ℝ × P → ℂ) (x : ℝ × P) : Fin (N + 1) → ℂ :=
  fun j => if 2 ≤ (j : ℕ) then T j x else 0

private def coefVec {P : Type} (N : ℕ) (e : ℕ → ℕ → ℂ) (T : ℕ → ℝ × P → ℂ) (k : Fin (N + 1)) : ℝ × P → ℂ :=
  fun x => Matrix.mulVec (padMatrix N e)⁻¹ (targetVec N T x) k

private def witness {P : Type} (L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (ψ : ℝ → ℝ) (φs : ℕ → ℝ → ℝ) (N : ℕ)
    (T : ℕ → ℝ × P → ℂ) : (Fin 2 → Fin 2 → ℝ) × P → ℂ := fun q =>
  L₀ q + L₁ q + ∑ k : Fin (N + 1), coefOfSq (coefVec N (entryFun φs) T k) k (Matrix.det (Matrix.of q.1), q.2) *
    (unitFamily (memberE ψ (φs k) k) (q.1, ()) - memberCorr ψ (φs k) k (q.1, ()))

private def corrFam {P : Type} (ψ : ℝ → ℝ) (φs : ℕ → ℝ → ℝ) (N : ℕ) (T : ℕ → ℝ × P → ℂ) (k : Fin (N + 1)) :
    (Fin 2 → Fin 2 → ℝ) × P → ℂ := fun q =>
  coefOfSq (coefVec N (entryFun φs) T k) k (Matrix.det (Matrix.of q.1), q.2) * adjuster ψ (φs k) k (q.1, ())

private theorem witness_eq {P : Type} (L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (ψ : ℝ → ℝ) (φs : ℕ → ℝ → ℝ)
    (N : ℕ) (T : ℕ → ℝ × P → ℂ) :
    witness L₀ L₁ ψ φs N T = L₀ + L₁ + ∑ k : Fin (N + 1), corrFam ψ φs N T k := by
  funext q
  simp only [witness, corrFam, adjuster, unitFamily, Pi.add_apply, Finset.sum_apply]

private structure Pieces {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (ψ : ℝ → ℝ) (φs : ℕ → ℝ → ℝ) (δ Δ : ℝ) (εs : ℕ → ℝ) (N : ℕ)
    (T : ℕ → ℝ × P → ℂ) (r₀ r₁ : ℝ) : Prop where
  hL₀ : ContDiff ℝ (⊤ : ℕ∞) L₀
  hL₀c : HasCompactSupport L₀
  hL₀inv : tsupport L₀ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}
  hL₁ : ContDiff ℝ (⊤ : ℕ∞) L₁
  hL₁c : HasCompactSupport L₁
  hL₁inv : tsupport L₁ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}
  hP : ∀ k, Profiles ψ (φs k) δ Δ (εs k)
  hT : ∀ j : ℕ, 2 ≤ j → ContDiff ℝ (⊤ : ℕ∞) (T j)
  hTc : ∀ j : ℕ, 2 ≤ j → HasCompactSupport (T j)
  hr₀ : 0 < r₀
  hT0 : ∀ j : ℕ, 2 ≤ j → j ≤ N → ∀ (r : ℝ) (p : P), (r ≤ r₀ ∨ r₁ ≤ r) → T j (r, p) = 0
  he : ∀ k : ℕ, 2 ≤ k → k ≤ N → entryFun φs k k ≠ 0
  hψ1 : ∀ x ∈ Set.Icc (r₀ ^ 2) (r₁ ^ 2), ψ x = 1

private theorem targetVec_eq_zero {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) {r : ℝ} (hr : r ≤ r₀ ∨ r₁ ≤ r)
    (p : P) : targetVec N T (r, p) = 0 := by
  funext j
  simp only [targetVec, Pi.zero_apply]
  split_ifs with hj
  · exact hW.hT0 j hj (Nat.lt_succ_iff.mp j.isLt) r p hr
  · rfl

private theorem coefVec_eq_zero {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) {r : ℝ}
    (hr : r ≤ r₀ ∨ r₁ ≤ r) (p : P) : coefVec N (entryFun φs) T k (r, p) = 0 := by
  simp only [coefVec, targetVec_eq_zero hW hr p, Matrix.mulVec_zero, Pi.zero_apply]

private theorem coefVec_eq_sum {P : Type} (N : ℕ) (e : ℕ → ℕ → ℂ) (T : ℕ → ℝ × P → ℂ) (k : Fin (N + 1)) :
    coefVec N e T k = fun x => ∑ j : Fin (N + 1), (padMatrix N e)⁻¹ k j * targetVec N T x j := by
  funext x
  simp only [coefVec, Matrix.mulVec, dotProduct]

private theorem contDiff_coefVec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (coefVec N (entryFun φs) T k) := by
  rw [coefVec_eq_sum]
  refine ContDiff.sum fun j _ => contDiff_const.mul ?_
  by_cases hj : 2 ≤ (j : ℕ)
  · have hfun : (fun x : ℝ × P => targetVec N T x j) = T j := by
      funext x
      simp only [targetVec, if_pos hj]
    rw [hfun]
    exact hW.hT j hj
  · have hfun : (fun x : ℝ × P => targetVec N T x j) = fun _ => 0 := by
      funext x
      simp only [targetVec, if_neg hj]
    rw [hfun]
    exact contDiff_const

private theorem hasCompactSupport_coefVec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) :
    HasCompactSupport (coefVec N (entryFun φs) T k) := by
  have hc : ∀ j : Fin (N + 1), HasCompactSupport fun x : ℝ × P => targetVec N T x j := by
    intro j
    by_cases hj : 2 ≤ (j : ℕ)
    · have hfun : (fun x : ℝ × P => targetVec N T x j) = T j := by
        funext x
        simp only [targetVec, if_pos hj]
      rw [hfun]
      exact hW.hTc j hj
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_empty fun x hx =>
        (hx (by simp only [targetVec, if_neg hj])).elim
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_iUnion fun j => (hc j).isCompact) fun x hx => ?_
  rw [Function.mem_support] at hx
  by_contra hx'
  simp only [Set.mem_iUnion, not_exists] at hx'
  have h0 : targetVec N T x = 0 := by
    funext j
    have hj := image_eq_zero_of_notMem_tsupport (hx' j)
    exact hj
  exact hx (by simp only [coefVec, h0, Matrix.mulVec_zero, Pi.zero_apply])

private theorem contDiff_det_prod {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ContDiff ℝ (⊤ : ℕ∞) fun q : (Fin 2 → Fin 2 → ℝ) × P => ((Matrix.det (Matrix.of q.1), q.2) : ℝ × P) := by
  have h : (fun q : (Fin 2 → Fin 2 → ℝ) × P => ((Matrix.det (Matrix.of q.1), q.2) : ℝ × P)) =
      fun q => (detE q.1, q.2) := by
    funext q
    rw [det_of]
  rw [h]
  exact (contDiff_detE.comp contDiff_fst).prodMk contDiff_snd

private theorem contDiff_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (corrFam ψ φs N T k) := by
  have hX : ContDiff ℝ (⊤ : ℕ∞) (coefOfSq (coefVec N (entryFun φs) T k) k) :=
    contDiff_coefOfSq _ (contDiff_coefVec hW k) k hW.hr₀ fun r p hr => coefVec_eq_zero hW k (Or.inl hr) p
  have hXd : ContDiff ℝ (⊤ : ℕ∞) fun q : (Fin 2 → Fin 2 → ℝ) × P =>
      coefOfSq (coefVec N (entryFun φs) T k) k (Matrix.det (Matrix.of q.1), q.2) :=
    hX.comp contDiff_det_prod
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun q : (Fin 2 → Fin 2 → ℝ) × P => adjuster ψ (φs k) k (q.1, ()) :=
    (contDiff_adjuster (hW.hP k) k).comp (contDiff_fst.prodMk contDiff_const)
  unfold corrFam
  exact hXd.mul hA

private theorem hasCompactSupport_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) :
    HasCompactSupport (corrFam ψ φs N T k) := by
  have hXc : HasCompactSupport (coefOfSq (coefVec N (entryFun φs) T k) k) :=
    hasCompactSupport_coefOfSq _ (hasCompactSupport_coefVec hW k) k hW.hr₀
      fun r p hr => coefVec_eq_zero hW k (Or.inl hr) p
  have hAc : HasCompactSupport (adjuster ψ (φs k) k) := hasCompactSupport_adjuster (hW.hP k) k
  refine HasCompactSupport.of_support_subset_isCompact
    ((hAc.isCompact.image continuous_fst).prod (hXc.isCompact.image continuous_snd)) fun q hq => ?_
  rw [Function.mem_support] at hq
  unfold corrFam at hq
  have hA : adjuster ψ (φs k) k (q.1, ()) ≠ 0 := right_ne_zero_of_mul hq
  have hX : coefOfSq (coefVec N (entryFun φs) T k) k (Matrix.det (Matrix.of q.1), q.2) ≠ 0 :=
    left_ne_zero_of_mul hq
  exact ⟨⟨(q.1, ()), subset_tsupport _ (Function.mem_support.mpr hA), rfl⟩,
    ⟨(Matrix.det (Matrix.of q.1), q.2), subset_tsupport _ (Function.mem_support.mpr hX), rfl⟩⟩

private theorem tsupport_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) :
    tsupport (corrFam ψ φs N T k) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  intro q hq
  unfold corrFam at hq
  have h1 : q ∈ tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => adjuster ψ (φs k) k (q.1, ()) :=
    tsupport_mul_subset_right hq
  have hπ : Continuous fun q : (Fin 2 → Fin 2 → ℝ) × P => ((q.1, ()) : (Fin 2 → Fin 2 → ℝ) × Unit) :=
    continuous_fst.prodMk continuous_const
  have h2 : q ∈ (fun q : (Fin 2 → Fin 2 → ℝ) × P => ((q.1, ()) : (Fin 2 → Fin 2 → ℝ) × Unit)) ⁻¹'
      tsupport (adjuster ψ (φs k) k) :=
    hπ.closure_preimage_subset (Function.support (adjuster ψ (φs k) k)) h1
  exact tsupport_adjuster (hW.hP k) k h2

private theorem tsupport_sum_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) :
    tsupport (∑ k : Fin (N + 1), corrFam ψ φs N T k) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  have hS : tsupport (∑ k : Fin (N + 1), corrFam ψ φs N T k) ⊆ ⋃ k : Fin (N + 1), tsupport (corrFam ψ φs N T k) := by
    refine closure_minimal (fun x hx => ?_) (isClosed_iUnion_of_finite fun k => isClosed_tsupport _)
    rw [Function.mem_support, Finset.sum_apply] at hx
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact Set.mem_iUnion.mpr ⟨k, subset_tsupport _ (Function.mem_support.mpr hk)⟩
  intro q hq
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hS hq)
  exact tsupport_corrFam hW k hk

private theorem tsupport_add_subset {P : Type} [TopologicalSpace P] (f g : (Fin 2 → Fin 2 → ℝ) × P → ℂ) :
    tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
  intro x hx
  have h := closure_mono (Function.support_add f g) hx
  rwa [closure_union] at h

private theorem contDiff_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) :
    ContDiff ℝ (⊤ : ℕ∞) (witness L₀ L₁ ψ φs N T) := by
  have hS : ContDiff ℝ (⊤ : ℕ∞) fun q : (Fin 2 → Fin 2 → ℝ) × P => ∑ k : Fin (N + 1), corrFam ψ φs N T k q :=
    ContDiff.sum fun k _ => contDiff_corrFam hW k
  have hfun : witness L₀ L₁ ψ φs N T = fun q => L₀ q + L₁ q + ∑ k : Fin (N + 1), corrFam ψ φs N T k q := by
    rw [witness_eq]
    funext q
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  exact (hW.hL₀.add hW.hL₁).add hS

private theorem hasCompactSupport_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) :
    HasCompactSupport (witness L₀ L₁ ψ φs N T) := by
  rw [witness_eq]
  exact hasCompactSupport_add (hasCompactSupport_add hW.hL₀c hW.hL₁c)
    (hasCompactSupport_sum Finset.univ _ fun k _ => hasCompactSupport_corrFam hW k)

private theorem tsupport_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) :
    tsupport (witness L₀ L₁ ψ φs N T) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  rw [witness_eq]
  intro q hq
  rcases tsupport_add_subset _ _ hq with h | h
  · rcases tsupport_add_subset _ _ h with h' | h'
    · exact hW.hL₀inv h'
    · exact hW.hL₁inv h'
  · exact tsupport_sum_corrFam hW h

private theorem splitTransform_entrySlice_detMul₂ {P : Type} [NormedAddCommGroup P] (X : ℝ × P → ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (a₁ a₂ : ℝ) :
    splitTransform (entrySlice (fun q => X (Matrix.det (Matrix.of q.1), q.2) * Φ q) p) a₁ a₂ =
      X (a₁ * a₂, p) * splitTransform (entrySlice Φ p) a₁ a₂ := by
  have h : entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => X (Matrix.det (Matrix.of q.1), q.2) * Φ q) p =
      entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => (fun d : ℝ => X (d, p)) (Matrix.det (Matrix.of q.1)) * Φ q)
        p := by
    funext g
    rfl
  rw [h]
  exact splitTransform_entrySlice_detMul (fun d : ℝ => X (d, p)) Φ p a₁ a₂

private theorem pairingE_detMul₂ {P : Type} [NormedAddCommGroup P] (X : ℝ × P → ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (j : ℕ) (p : P) {r : ℝ} (hr : 0 < r) :
    pairingE j (fun q => X (Matrix.det (Matrix.of q.1), q.2) * Φ q) p r = X (r ^ 2, p) * pairingE j Φ p r := by
  have h : pairingE j (fun q : (Fin 2 → Fin 2 → ℝ) × P => X (Matrix.det (Matrix.of q.1), q.2) * Φ q) p r =
      pairingE j (fun q : (Fin 2 → Fin 2 → ℝ) × P => (fun d : ℝ => X (d, p)) (Matrix.det (Matrix.of q.1)) * Φ q)
        p r := by
    unfold pairingE
    rfl
  rw [h]
  exact pairingE_detMul (fun d : ℝ => X (d, p)) Φ j p hr

private theorem entrySlice_adjuster_prod {P : Type} (ψ φ : ℝ → ℝ) (k : ℕ) (p : P) :
    entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => adjuster ψ φ k (q.1, ())) p = entrySlice (adjuster ψ φ k) () := by
  funext g
  rfl

private theorem splitTransform_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) (p : P)
    {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) : splitTransform (entrySlice (corrFam ψ φs N T k) p) a₁ a₂ = 0 := by
  unfold corrFam
  rw [splitTransform_entrySlice_detMul₂ (coefOfSq (coefVec N (entryFun φs) T k) k)
    (fun q : (Fin 2 → Fin 2 → ℝ) × P => adjuster ψ (φs k) k (q.1, ())) p a₁ a₂, entrySlice_adjuster_prod,
    splitTransform_adjuster (hW.hP k) k () h, mul_zero]

private theorem splitTransform_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (H : ℝ × ℝ × P → ℂ)
    (hsplit : ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice (L₀ + L₁) p) a₁ a₂ = H (a₁, a₂, p))
    (p : P) {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) :
    splitTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) a₁ a₂ = H (a₁, a₂, p) := by
  have hLc : Continuous (L₀ + L₁) := hW.hL₀.continuous.add hW.hL₁.continuous
  have hLs : HasCompactSupport (L₀ + L₁) := hasCompactSupport_add hW.hL₀c hW.hL₁c
  have hCc : ∀ k ∈ (Finset.univ : Finset (Fin (N + 1))), Continuous (corrFam ψ φs N T k) :=
    fun k _ => (contDiff_corrFam hW k).continuous
  have hCs : ∀ k ∈ (Finset.univ : Finset (Fin (N + 1))), HasCompactSupport (corrFam ψ φs N T k) :=
    fun k _ => hasCompactSupport_corrFam hW k
  rw [witness_eq, splitTransform_entrySlice_add (L₀ + L₁) _ hLc hLs (continuous_sum _ _ hCc)
    (hasCompactSupport_sum _ _ hCs), splitTransform_entrySlice_sum _ _ hCc hCs, hsplit p a₁ a₂ h,
    Finset.sum_eq_zero fun k _ => splitTransform_corrFam hW k p h, add_zero]

private theorem pairingE_corrFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (_hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (k : Fin (N + 1)) (j : ℕ) (p : P)
    {r : ℝ} (hr : 0 < r) :
    pairingE j (corrFam ψ φs N T k) p r =
      coefOfSq (coefVec N (entryFun φs) T k) k (r ^ 2, p) * pairingE j (adjuster ψ (φs k) k) () r := by
  unfold corrFam
  rw [pairingE_detMul₂ (coefOfSq (coefVec N (entryFun φs) T k) k)
    (fun q : (Fin 2 → Fin 2 → ℝ) × P => adjuster ψ (φs k) k (q.1, ())) j p hr]
  unfold pairingE
  rw [entrySlice_adjuster_prod]

private theorem pairingE_witness_eq_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁)
    (hLpair : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r → pairingE j (L₀ + L₁) p r = 0)
    (j : ℕ) (hj : 2 ≤ j) (p : P) {r : ℝ} (hr : 0 < r) :
    pairingE j (witness L₀ L₁ ψ φs N T) p r = ∑ k : Fin (N + 1),
      coefOfSq (coefVec N (entryFun φs) T k) k (r ^ 2, p) * pairingE j (adjuster ψ (φs k) k) () r := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (L₀ + L₁) := hW.hL₀.add hW.hL₁
  have hLs : HasCompactSupport (L₀ + L₁) := hasCompactSupport_add hW.hL₀c hW.hL₁c
  have hLinv : tsupport (L₀ + L₁) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := fun q hq => by
    rcases tsupport_add_subset _ _ hq with h | h
    · exact hW.hL₀inv h
    · exact hW.hL₁inv h
  have hSfun : (∑ k : Fin (N + 1), corrFam ψ φs N T k) = fun q => ∑ k : Fin (N + 1), corrFam ψ φs N T k q := by
    funext q
    exact Finset.sum_apply q _ _
  have hS : ContDiff ℝ (⊤ : ℕ∞) (∑ k : Fin (N + 1), corrFam ψ φs N T k) := by
    rw [hSfun]
    exact ContDiff.sum fun k _ => contDiff_corrFam hW k
  have hSs : HasCompactSupport (∑ k : Fin (N + 1), corrFam ψ φs N T k) :=
    hasCompactSupport_sum _ _ fun k _ => hasCompactSupport_corrFam hW k
  obtain ⟨hEL, hHL⟩ := pairing_layers_integrable (L₀ + L₁) hL hLs hLinv j p hr
  obtain ⟨hES, hHS⟩ :=
    pairing_layers_integrable (∑ k : Fin (N + 1), corrFam ψ φs N T k) hS hSs (tsupport_sum_corrFam hW) j p hr
  have hk : ∀ k : Fin (N + 1),
      IntervalIntegrable (fun θ => ellipticTransform (entrySlice (corrFam ψ φs N T k) p) r θ *
          (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi ∧
        Integrable fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ) *
          (splitTransform (entrySlice (corrFam ψ φs N T k) p) (r * Real.exp t) (r * Real.exp (-t)) +
            (-1 : ℂ) ^ j * splitTransform (entrySlice (corrFam ψ φs N T k) p)
              (-(r * Real.exp t)) (-(r * Real.exp (-t)))) :=
    fun k => pairing_layers_integrable (corrFam ψ φs N T k) (contDiff_corrFam hW k) (hasCompactSupport_corrFam hW k)
      (tsupport_corrFam hW k) j p hr
  rw [witness_eq, pairingE_add_pi (L₀ + L₁) _ hL.continuous hLs hS.continuous hSs j p r hEL hES hHL hHS,
    hLpair j hj p r hr, zero_add,
    pairingE_sum_pi Finset.univ (fun k => corrFam ψ φs N T k) (fun k _ => (contDiff_corrFam hW k).continuous)
      (fun k _ => hasCompactSupport_corrFam hW k) j p r (fun k _ => (hk k).1) (fun k _ => (hk k).2)]
  exact Finset.sum_congr rfl fun k _ => pairingE_corrFam hW k j p hr

private theorem pairingE_witness_of_le {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁)
    (hLpair : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r → pairingE j (L₀ + L₁) p r = 0)
    (j : Fin (N + 1)) (hj : 2 ≤ (j : ℕ)) (p : P) {r : ℝ} (hr : 0 < r) :
    pairingE j (witness L₀ L₁ ψ φs N T) p r = T j (r, p) := by
  rw [pairingE_witness_eq_sum hW hLpair j hj p hr]
  have hterm : ∀ k : Fin (N + 1),
      coefOfSq (coefVec N (entryFun φs) T k) k (r ^ 2, p) * pairingE j (adjuster ψ (φs k) k) () r =
        (ψ (r ^ 2) : ℂ) * (padMatrix N (entryFun φs) j k * coefVec N (entryFun φs) T k (r, p)) := by
    intro k
    rw [coefOfSq_sq _ _ hr, pairingE_adjuster hW.hP N j k hj () hr]
    have hr0 : (r : ℂ) ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
    field_simp
  have hinv : ∑ k : Fin (N + 1), padMatrix N (entryFun φs) j k * coefVec N (entryFun φs) T k (r, p) =
      targetVec N T (r, p) j :=
    padMatrix_mulVec_inv N (entryFun φs) hW.he (targetVec N T (r, p)) j
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, hinv]
  simp only [targetVec, if_pos hj]
  by_cases hwin : r₀ ≤ r ∧ r ≤ r₁
  · rw [hW.hψ1 (r ^ 2) ⟨pow_le_pow_left₀ hW.hr₀.le hwin.1 2, pow_le_pow_left₀ hr.le hwin.2 2⟩,
      Complex.ofReal_one, one_mul]
  · have h0 : T j (r, p) = 0 := by
      refine hW.hT0 j hj (Nat.lt_succ_iff.mp j.isLt) r p ?_
      rcases not_and_or.mp hwin with h | h
      · exact Or.inl (not_le.mp h).le
      · exact Or.inr (not_le.mp h).le
    rw [h0, mul_zero]

private theorem pairingE_witness_of_lt {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁)
    (hLpair : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r → pairingE j (L₀ + L₁) p r = 0)
    {j : ℕ} (hj : 2 ≤ j) (hNj : N < j) (p : P) {r : ℝ} (hr : 0 < r) :
    pairingE j (witness L₀ L₁ ψ φs N T) p r = 0 := by
  rw [pairingE_witness_eq_sum hW hLpair j hj p hr]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pairingE_adjuster_eq_zero (hW.hP k) (lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) hNj) hj () hr, mul_zero]

private theorem mode_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁)
    (hLpair : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r → pairingE j (L₀ + L₁) p r = 0)
    (E : ℝ × ℝ × P → ℂ) (D : ℕ → P → ℝ → ℂ)
    (hmode : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r →
      (∫ θ in (0 : ℝ)..Real.pi, E (r, θ, p) * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) -
          (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ *
            (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        D j p r - pairingE j (witness L₀ L₁ ψ φs N T) p r)
    (hTD : ∀ j : ℕ, 2 ≤ j → j ≤ N → ∀ (p : P) (r : ℝ), 0 < r → T j (r, p) = D j p r)
    (hD : ∀ (p : P) (j : ℕ), N < j → ∀ r : ℝ, 0 < r → D j p r = 0) {j : ℕ} (hj : 2 ≤ j) (p : P) {r : ℝ}
    (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ *
        (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      ∫ θ in (0 : ℝ)..Real.pi, E (r, θ, p) * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
  have hpair : pairingE j (witness L₀ L₁ ψ φs N T) p r = D j p r := by
    by_cases hjN : j ≤ N
    · exact (pairingE_witness_of_le hW hLpair ⟨j, Nat.lt_succ_of_le hjN⟩ hj p hr).trans (hTD j hj hjN p r hr)
    · exact (pairingE_witness_of_lt hW hLpair hj (not_le.mp hjN) p hr).trans (hD p j (not_le.mp hjN) r hr).symm
  have h := hmode j hj p r hr
  rw [hpair, sub_self, sub_eq_zero] at h
  exact h.symm

private theorem ellipticTransform_witness {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {L₀ L₁ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {ψ : ℝ → ℝ} {φs : ℕ → ℝ → ℝ} {δ Δ : ℝ} {εs : ℕ → ℝ} {N : ℕ}
    {T : ℕ → ℝ × P → ℂ} {r₀ r₁ : ℝ} (hW : Pieces L₀ L₁ ψ φs δ Δ εs N T r₀ r₁) (E : ℝ × ℝ × P → ℂ)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (hEcont : ContinuousOn E {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi}) (p : P) {r : ℝ} (hr : 0 < r)
    (hm : ∀ j : ℕ, 2 ≤ j →
      (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ *
          (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        ∫ θ in (0 : ℝ)..Real.pi, E (r, θ, p) * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ = E (r, θ, p) := by
  obtain ⟨hcont, hbound⟩ := ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin P
    (witness L₀ L₁ ψ φs N T) (contDiff_witness hW).continuous (hasCompactSupport_witness hW) (tsupport_witness hW)
  obtain ⟨K, hK⟩ := hbound {r} isCompact_singleton (Set.singleton_subset_iff.mpr hr)
  have hι : Continuous fun θ : ℝ => ((r, θ, p) : ℝ × ℝ × P) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hA : ContinuousOn (fun θ : ℝ => ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ)
      (Set.Ioo 0 Real.pi) :=
    hcont.comp hι.continuousOn fun θ hθ => ⟨hr, hθ.1, hθ.2⟩
  have hAb : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ‖ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ‖ ≤ |K| :=
    fun θ hθ => (hK r (Set.mem_singleton r) θ hθ p).trans ((mul_le_mul_of_nonneg_right (le_abs_self K)
      (abs_nonneg _)).trans (mul_le_of_le_one_right (abs_nonneg K) (Real.abs_sin_le_one θ)))
  have hB : ContinuousOn (fun θ : ℝ => E (r, θ, p)) (Set.Ioo 0 Real.pi) :=
    hEcont.comp hι.continuousOn fun θ hθ => ⟨hr, hθ.1, hθ.2⟩
  have hmodes : ∀ n : ℕ,
      (∫ θ in (0 : ℝ)..Real.pi, ellipticTransform (entrySlice (witness L₀ L₁ ψ φs N T) p) r θ *
          (((Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) =
        ∫ θ in (0 : ℝ)..Real.pi, E (r, θ, p) * (((Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) := by
    intro n
    have h := hm (n + 2) (Nat.le_add_left 2 n)
    have hidx : (((n + 2 : ℕ) : ℤ) - 2) = (n : ℤ) := by omega
    rw [hidx] at h
    exact h
  exact eqOn_Ioo_of_modes_eq _ _ |K| hA hAb hB (hEi r p) hmodes θ ⟨hθ0, hθπ⟩

private theorem contDiff_slice {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {G : ℝ × ℝ × P → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p : P) : ContDiff ℝ (⊤ : ℕ∞) fun a : ℝ × ℝ => G (a.1, a.2, p) :=
  hG.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

private theorem hasCompactSupport_slice {P : Type} [TopologicalSpace P] {G : ℝ × ℝ × P → ℂ}
    (hGc : HasCompactSupport G) (p : P) : HasCompactSupport fun a : ℝ × ℝ => G (a.1, a.2, p) :=
  HasCompactSupport.of_support_subset_isCompact
    (hGc.isCompact.image (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) fun a ha =>
    ⟨(a.1, a.2, p), subset_tsupport _ (Function.mem_support.mpr (Function.mem_support.mp ha)), rfl⟩

private theorem hasCompactSupport_fun_sum {ι : Type} (s : Finset ι) (g : ι → ℝ × ℝ → ℂ)
    (hg : ∀ i ∈ s, HasCompactSupport (g i)) : HasCompactSupport fun x => ∑ i ∈ s, g i x := by
  refine HasCompactSupport.of_support_subset_isCompact (s.isCompact_biUnion fun i hi => (hg i hi).isCompact) ?_
  intro x hx
  rw [Function.mem_support] at hx
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact Set.mem_iUnion₂.mpr ⟨i, hi, subset_tsupport _ (Function.mem_support.mpr hne)⟩

private def Hplus {P : Type} (H : ℝ × ℝ × P → ℂ) : ℝ × ℝ × P → ℂ :=
  fun q => (H q + H (-q.1, -q.2.1, q.2.2)) / 2

private def Hminus {P : Type} (H : ℝ × ℝ × P → ℂ) : ℝ × ℝ × P → ℂ :=
  fun q => (H q - H (-q.1, -q.2.1, q.2.2)) / 2

private def signedPart {P : Type} (ε : ℂ) (H : ℝ × ℝ × P → ℂ) : ℝ × ℝ × P → ℂ :=
  fun q => (H q + ε * H (-q.1, -q.2.1, q.2.2)) / 2

private theorem signedPart_admissible {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) (ε : ℂ) (hε : ε * ε = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (signedPart ε H) ∧ HasCompactSupport (signedPart ε H) ∧
      tsupport (signedPart ε H) ⊆ {q | q.1 * q.2.1 ≠ 0} ∧
      (∀ (a₁ a₂ : ℝ) (p : P), signedPart ε H (a₂, a₁, p) = signedPart ε H (a₁, a₂, p)) ∧
      ∀ (a₁ a₂ : ℝ) (p : P), signedPart ε H (-a₁, -a₂, p) = ε * signedPart ε H (a₁, a₂, p) := by
  have hNc : ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × ℝ × P => ((-q.1, -q.2.1, q.2.2) : ℝ × ℝ × P) :=
    contDiff_fst.neg.prodMk ((contDiff_fst.comp contDiff_snd).neg.prodMk (contDiff_snd.comp contDiff_snd))
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (signedPart ε H) := (hH.add (contDiff_const.mul (hH.comp hNc))).div_const 2

  have hK : Function.support (signedPart ε H) ⊆
      tsupport H ∪ (fun q : ℝ × ℝ × P => ((-q.1, -q.2.1, q.2.2) : ℝ × ℝ × P)) '' tsupport H := by
    intro q hq
    rw [Function.mem_support] at hq
    by_cases h0 : H q = 0
    · right
      have h1 : H (-q.1, -q.2.1, q.2.2) ≠ 0 := by
        intro h1
        apply hq
        simp only [signedPart, h0, h1, mul_zero, add_zero, zero_div]
      exact ⟨(-q.1, -q.2.1, q.2.2), subset_tsupport _ (Function.mem_support.mpr h1),
        Prod.ext (neg_neg _) (Prod.ext (neg_neg _) rfl)⟩
    · left
      exact subset_tsupport _ (Function.mem_support.mpr h0)
  have hKc : IsCompact (tsupport H ∪ (fun q : ℝ × ℝ × P => ((-q.1, -q.2.1, q.2.2) : ℝ × ℝ × P)) '' tsupport H) :=
    hHc.isCompact.union (hHc.isCompact.image hNc.continuous)
  refine ⟨h1, HasCompactSupport.of_support_subset_isCompact hKc hK, ?_, ?_, ?_⟩
  · refine (closure_minimal hK hKc.isClosed).trans (Set.union_subset hHsupp ?_)
    rintro _ ⟨x, hx, rfl⟩
    show -x.1 * -x.2.1 ≠ 0
    rw [neg_mul_neg]
    exact hHsupp hx
  · intro a₁ a₂ p
    simp only [signedPart]
    rw [hHsym a₁ a₂ p, hHsym (-a₁) (-a₂) p]
  · intro a₁ a₂ p
    simp only [signedPart, neg_neg]
    linear_combination (-(H (-a₁, -a₂, p) / 2)) * hε

private theorem Hplus_admissible {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) :
    ContDiff ℝ (⊤ : ℕ∞) (Hplus H) ∧ HasCompactSupport (Hplus H) ∧ tsupport (Hplus H) ⊆ {q | q.1 * q.2.1 ≠ 0} ∧
      (∀ (a₁ a₂ : ℝ) (p : P), Hplus H (a₂, a₁, p) = Hplus H (a₁, a₂, p)) ∧
      ∀ (a₁ a₂ : ℝ) (p : P), Hplus H (-a₁, -a₂, p) = 1 * Hplus H (a₁, a₂, p) := by
  have e : Hplus H = signedPart 1 H := by
    funext q
    simp only [Hplus, signedPart, one_mul]
  rw [e]
  exact signedPart_admissible H hH hHc hHsupp hHsym 1 (one_mul 1)

private theorem Hminus_admissible {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) :
    ContDiff ℝ (⊤ : ℕ∞) (Hminus H) ∧ HasCompactSupport (Hminus H) ∧ tsupport (Hminus H) ⊆ {q | q.1 * q.2.1 ≠ 0} ∧
      (∀ (a₁ a₂ : ℝ) (p : P), Hminus H (a₂, a₁, p) = Hminus H (a₁, a₂, p)) ∧
      ∀ (a₁ a₂ : ℝ) (p : P), Hminus H (-a₁, -a₂, p) = -1 * Hminus H (a₁, a₂, p) := by
  have e : Hminus H = signedPart (-1) H := by
    funext q
    simp only [Hminus, signedPart]
    ring
  rw [e]
  exact signedPart_admissible H hH hHc hHsupp hHsym (-1) (by norm_num)

private structure IsRealiserAt (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (m : ℤ) (sgn : ℂ)
    (I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ)) : Prop where
  lin : ∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M
  real : ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
    tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
    (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
    (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = sgn * H (a₁, a₂, p)) →
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
    HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
    tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
      {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
    (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
          ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ m k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ m k₂ : ℂˣ) : ℂ) *
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
    ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
      splitTransform
          (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
          a₁ a₂ = H (a₁, a₂, p)

private theorem exists_isRealiserAt_zero (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ I, IsRealiserAt P 0 1 I := by
  obtain ⟨I, hL, hI⟩ := exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq P
  exact ⟨I, hL, fun H h1 h2 h3 h4 h5 => hI H h1 h2 h3 h4 fun a₁ a₂ p => by rw [h5 a₁ a₂ p, one_mul]⟩

private theorem exists_isRealiserAt_one (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ I, IsRealiserAt P 1 (-1) I := by
  obtain ⟨I, hL, hI⟩ := exists_linear_entrySlice_archWeightChar_one_splitTransform_eq P
  exact ⟨I, hL, fun H h1 h2 h3 h4 h5 => hI H h1 h2 h3 h4 fun a₁ a₂ p => by rw [h5 a₁ a₂ p, neg_one_mul]⟩

private def dataRealiser0 (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ) :=
  Classical.choose (exists_isRealiserAt_zero P)

private def dataRealiser1 (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ) :=
  Classical.choose (exists_isRealiserAt_one P)

private theorem dataRealiser0_spec (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    IsRealiserAt P 0 1 (dataRealiser0 P) :=
  Classical.choose_spec (exists_isRealiserAt_zero P)

private theorem dataRealiser1_spec (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    IsRealiserAt P 1 (-1) (dataRealiser1 P) :=
  Classical.choose_spec (exists_isRealiserAt_one P)

private theorem realiser_zero {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℤ} {sgn : ℂ}
    {I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ)} (hI : IsRealiserAt P m sgn I) :
    I (fun _ => 0) = fun _ => 0 := by
  have hz : HasCompactSupport (fun _ : ℝ × ℝ => (0 : ℂ)) := HasCompactSupport.zero
  have h := hI.lin (fun _ => 0) (fun _ => 0) contDiff_const hz contDiff_const hz 0 0
  simp only [zero_mul, add_zero] at h
  exact h

private theorem realiser_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℤ} {sgn : ℂ}
    {I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ)} (hI : IsRealiserAt P m sgn I) {n : ℕ} (c : Fin n → ℂ)
    (f : Fin n → ℝ × ℝ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    I (fun x => ∑ i, c i * f i x) = fun M => ∑ i, c i * I (f i) M := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact realiser_zero hI
  | succ n ih =>
    have hgs : ContDiff ℝ (⊤ : ℕ∞) fun y : ℝ × ℝ => ∑ i : Fin n, c i.succ * f i.succ y :=
      ContDiff.sum fun i _ => contDiff_const.mul (hf i.succ)
    have hgc : HasCompactSupport fun y : ℝ × ℝ => ∑ i : Fin n, c i.succ * f i.succ y := by
      refine hasCompactSupport_fun_sum (Finset.univ : Finset (Fin n))
        (fun (i : Fin n) (y : ℝ × ℝ) => c i.succ * f i.succ y) ?_
      intro i _
      have h : HasCompactSupport fun y : ℝ × ℝ => c i.succ * f i.succ y := (hfc i.succ).mul_left
      exact h
    have hfun : (fun x : ℝ × ℝ => ∑ i : Fin (n + 1), c i * f i x) =
        fun x => c 0 * f 0 x + 1 * ∑ i : Fin n, c i.succ * f i.succ x := by
      funext x
      simp only [Fin.sum_univ_succ, one_mul]
    rw [hfun, hI.lin (f 0) (fun y => ∑ i : Fin n, c i.succ * f i.succ y) (hf 0) (hfc 0) hgs hgc (c 0) 1,
      ih (fun i => c i.succ) (fun i => f i.succ) (fun i => hf i.succ) (fun i => hfc i.succ)]
    funext M
    simp only [Fin.sum_univ_succ, one_mul]

private def dataLift0 {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ) :
    (Fin 2 → Fin 2 → ℝ) × P → ℂ :=
  fun q => dataRealiser0 P (fun a : ℝ × ℝ => Hplus H (a.1, a.2, q.2)) q.1

private def dataLift1 {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ) :
    (Fin 2 → Fin 2 → ℝ) × P → ℂ :=
  fun q => dataRealiser1 P (fun a : ℝ × ℝ => Hminus H (a.1, a.2, q.2)) q.1

private def dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ) :
    (Fin 2 → Fin 2 → ℝ) × P → ℂ :=
  dataLift0 H + dataLift1 H

private theorem dataLift_apply {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (q : (Fin 2 → Fin 2 → ℝ) × P) :
    dataLift H q = dataRealiser0 P (fun a : ℝ × ℝ => Hplus H (a.1, a.2, q.2)) q.1 +
      dataRealiser1 P (fun a : ℝ × ℝ => Hminus H (a.1, a.2, q.2)) q.1 :=
  rfl

private theorem dataLift0_props {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) :
    ContDiff ℝ (⊤ : ℕ∞) (dataLift0 H) ∧ HasCompactSupport (dataLift0 H) ∧
      tsupport (dataLift0 H) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
      (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        entrySlice (dataLift0 H) p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) * entrySlice (dataLift0 H) p g) ∧
      ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
        splitTransform (entrySlice (dataLift0 H) p) a₁ a₂ = Hplus H (a₁, a₂, p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Hplus_admissible H hH hHc hHsupp hHsym
  exact (dataRealiser0_spec P).real (Hplus H) h1 h2 h3 h4 h5

private theorem dataLift1_props {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) :
    ContDiff ℝ (⊤ : ℕ∞) (dataLift1 H) ∧ HasCompactSupport (dataLift1 H) ∧
      tsupport (dataLift1 H) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
      (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        entrySlice (dataLift1 H) p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) * entrySlice (dataLift1 H) p g) ∧
      ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
        splitTransform (entrySlice (dataLift1 H) p) a₁ a₂ = Hminus H (a₁, a₂, p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Hminus_admissible H hH hHc hHsupp hHsym
  exact (dataRealiser1_spec P).real (Hminus H) h1 h2 h3 h4 h5

private theorem contDiff_dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) : ContDiff ℝ (⊤ : ℕ∞) (dataLift H) := by
  rw [show dataLift H = fun q => dataLift0 H q + dataLift1 H q from rfl]
  exact (dataLift0_props H hH hHc hHsupp hHsym).1.add (dataLift1_props H hH hHc hHsupp hHsym).1

private theorem hasCompactSupport_dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) : HasCompactSupport (dataLift H) := by
  show HasCompactSupport (dataLift0 H + dataLift1 H)
  exact (dataLift0_props H hH hHc hHsupp hHsym).2.1.add (dataLift1_props H hH hHc hHsupp hHsym).2.1

private theorem tsupport_dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) :
    tsupport (dataLift H) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := by
  intro q hq
  have hs : Function.support (dataLift H) ⊆ Function.support (dataLift0 H) ∪ Function.support (dataLift1 H) :=
    Function.support_add (dataLift0 H) (dataLift1 H)
  have hq' : q ∈ tsupport (dataLift0 H) ∪ tsupport (dataLift1 H) := by
    have h := closure_mono hs hq
    rwa [closure_union] at h
  rcases hq' with h | h
  · exact (dataLift0_props H hH hHc hHsupp hHsym).2.2.1 h
  · exact (dataLift1_props H hH hHc hHsupp hHsym).2.2.1 h

private theorem splitTransform_dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) (p : P) {a₁ a₂ : ℝ} (h : a₁ * a₂ ≠ 0) :
    splitTransform (entrySlice (dataLift H) p) a₁ a₂ = H (a₁, a₂, p) := by
  have h0 := dataLift0_props H hH hHc hHsupp hHsym
  have h1 := dataLift1_props H hH hHc hHsupp hHsym
  have hadd := splitTransform_entrySlice_add (dataLift0 H) (dataLift1 H) h0.1.continuous h0.2.1 h1.1.continuous
    h1.2.1 p a₁ a₂
  show splitTransform (entrySlice (dataLift0 H + dataLift1 H) p) a₁ a₂ = H (a₁, a₂, p)
  rw [hadd, h0.2.2.2.2 p a₁ a₂ h, h1.2.2.2.2 p a₁ a₂ h]
  simp only [Hplus, Hminus]
  ring

private theorem intervalIntegrable_ellipticTransform_mul_U {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (p : P) {r : ℝ} (hr : 0 < r) (n : ℤ) :
    IntervalIntegrable (fun θ => ellipticTransform (entrySlice Φ p) r θ *
      (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi := by
  obtain ⟨hcont, hbound⟩ :=
    ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin P Φ hΦ hΦc hΦinv
  obtain ⟨K, hK⟩ := hbound {r} isCompact_singleton (Set.singleton_subset_iff.mpr hr)
  have hA : ContinuousOn (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ) (Set.Ioo 0 Real.pi) :=
    hcont.comp' (f := fun θ : ℝ => ((r, θ, p) : ℝ × ℝ × P)) (by fun_prop) fun θ hθ => ⟨hr, hθ.1, hθ.2⟩
  refine intervalIntegrable_mul_U_of_bound _ (max K 0) hA (fun θ hθ => ?_) n
  calc ‖ellipticTransform (entrySlice Φ p) r θ‖ ≤ K * |Real.sin θ| := hK r (Set.mem_singleton r) θ hθ p
    _ ≤ max K 0 * |Real.sin θ| := mul_le_mul_of_nonneg_right (le_max_left K 0) (abs_nonneg _)
    _ ≤ max K 0 * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (le_max_right K 0)
    _ = max K 0 := mul_one _

private theorem integrable_torus_of_splitTransform_eq {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (G : ℝ × ℝ × P → ℂ) (hG : Continuous G) (hGc : HasCompactSupport G) (p : P)
    (hS : ∀ a₁ a₂ : ℝ, a₁ * a₂ ≠ 0 → splitTransform (entrySlice Φ p) a₁ a₂ = G (a₁, a₂, p)) (w : ℝ → ℂ)
    (hw : Continuous w) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable fun t : ℝ => w t * (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
      c * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
  have hfun : (fun t : ℝ => w t * (splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) +
      c * splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))))) = fun t : ℝ =>
      w t * (G (r * Real.exp t, r * Real.exp (-t), p) + c * G (-(r * Real.exp t), -(r * Real.exp (-t)), p)) := by
    funext t
    rw [hS _ _ (by rw [torus_mul]; positivity), hS _ _ (by rw [torus_neg_mul]; positivity)]
  rw [hfun]
  exact integrable_torus (fun a : ℝ × ℝ => G (a.1, a.2, p))
    (hG.comp (by fun_prop : Continuous fun a : ℝ × ℝ => ((a.1, a.2, p) : ℝ × ℝ × P))) (hasCompactSupport_slice hGc p)
    w hw c hr

private theorem pairingE_dataLift {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) {j : ℕ} (hj : 2 ≤ j) (p : P) {r : ℝ}
    (hr : 0 < r) : pairingE j (dataLift H) p r = 0 := by
  have hp := Hplus_admissible H hH hHc hHsupp hHsym
  have hm := Hminus_admissible H hH hHc hHsupp hHsym
  have h0 := dataLift0_props H hH hHc hHsupp hHsym
  have h1 := dataLift1_props H hH hHc hHsupp hHsym

  have hE0 := intervalIntegrable_ellipticTransform_mul_U (dataLift0 H) h0.1.continuous h0.2.1 h0.2.2.1 p hr
    ((j : ℤ) - 2)
  have hE1 := intervalIntegrable_ellipticTransform_mul_U (dataLift1 H) h1.1.continuous h1.2.1 h1.2.2.1 p hr
    ((j : ℤ) - 2)
  have hw : Continuous fun t : ℝ => ((Real.exp (-(((j : ℝ) - 1) * |t|)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)
  have hH0 := integrable_torus_of_splitTransform_eq (dataLift0 H) (Hplus H) hp.1.continuous hp.2.1 p
    (h0.2.2.2.2 p) _ hw ((-1 : ℂ) ^ j) hr
  have hH1 := integrable_torus_of_splitTransform_eq (dataLift1 H) (Hminus H) hm.1.continuous hm.2.1 p
    (h1.2.2.2.2 p) _ hw ((-1 : ℂ) ^ j) hr
  have hadd := pairingE_add (dataLift0 H) (dataLift1 H) h0.1.continuous h0.2.1 h1.1.continuous h1.2.1 j p r hE0
    hE1 hH0 hH1

  have hz0 : pairingE j (dataLift0 H) p r = 0 :=
    (discreteSeriesPairing_entrySlice_eq_zero_of_weight P 0 (dataLift0 H) h0.1 h0.2.1 h0.2.2.1
      (fun p k₁ k₂ g => by rw [Nat.cast_zero]; exact h0.2.2.2.1 p k₁ k₂ g) p).1 j (by omega) r hr
  have hz1 : pairingE j (dataLift1 H) p r = 0 := by
    have hU := discreteSeriesPairing_entrySlice_eq_zero_of_weight P 1 (dataLift1 H) h1.1 h1.2.1 h1.2.2.1
      (fun p k₁ k₂ g => by rw [Nat.cast_one]; exact h1.2.2.2.1 p k₁ k₂ g) p
    by_cases hj3 : 3 ≤ j
    · exact hU.1 j (by omega) r hr
    · obtain rfl : j = 2 := by omega
      exact hU.2 2 le_rfl (by omega) r hr
  have hlam : dataLift H = fun q => dataLift0 H q + dataLift1 H q := rfl
  rw [hlam, hadd, hz0, hz1, add_zero]

private theorem sum_mul_dataLift_eq_zero {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (H : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) {n : ℕ} (c : Fin n → ℂ) (q : Fin n → P)
    (hrel : ∀ a : ℝ × ℝ, ∑ i, c i * H (a.1, a.2, q i) = 0) (M : Fin 2 → Fin 2 → ℝ) :
    ∑ i, c i * dataLift H (M, q i) = 0 := by
  have hp := Hplus_admissible H hH hHc hHsupp hHsym
  have hm := Hminus_admissible H hH hHc hHsupp hHsym

  have hsum0 := realiser_sum (dataRealiser0_spec P) c (fun i => fun a : ℝ × ℝ => Hplus H (a.1, a.2, q i))
    (fun i => contDiff_slice hp.1 (q i)) fun i => hasCompactSupport_slice hp.2.1 (q i)
  have hsum1 := realiser_sum (dataRealiser1_spec P) c (fun i => fun a : ℝ × ℝ => Hminus H (a.1, a.2, q i))
    (fun i => contDiff_slice hm.1 (q i)) fun i => hasCompactSupport_slice hm.2.1 (q i)

  have hrel0 : (fun x : ℝ × ℝ => ∑ i, c i * Hplus H (x.1, x.2, q i)) = fun _ => 0 := by
    funext x
    have ha := hrel x
    have hb := hrel (-x.1, -x.2)
    dsimp only at hb
    have hterm : ∀ i ∈ Finset.univ, c i * Hplus H (x.1, x.2, q i) =
        (c i * H (x.1, x.2, q i) + c i * H (-x.1, -x.2, q i)) / 2 := fun i _ => by
      simp only [Hplus]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_add_distrib, ha, hb, add_zero, zero_div]
  have hrel1 : (fun x : ℝ × ℝ => ∑ i, c i * Hminus H (x.1, x.2, q i)) = fun _ => 0 := by
    funext x
    have ha := hrel x
    have hb := hrel (-x.1, -x.2)
    dsimp only at hb
    have hterm : ∀ i ∈ Finset.univ, c i * Hminus H (x.1, x.2, q i) =
        (c i * H (x.1, x.2, q i) - c i * H (-x.1, -x.2, q i)) / 2 := fun i _ => by
      simp only [Hminus]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib, ha, hb, sub_zero, zero_div]
  show ∑ i, c i * (dataRealiser0 P (fun a : ℝ × ℝ => Hplus H (a.1, a.2, q i)) M +
    dataRealiser1 P (fun a : ℝ × ℝ => Hminus H (a.1, a.2, q i)) M) = 0
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← congrFun hsum0 M, ← congrFun hsum1 M, hrel0, hrel1, realiser_zero (dataRealiser0_spec P),
    realiser_zero (dataRealiser1_spec P), add_zero]

private def modeE {P : Type} (E : ℝ × ℝ × P → ℂ) (k : ℕ) : ℝ × P → ℂ := fun q =>
  ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)

private def modeFam {P : Type} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) : ℝ × P → ℂ := fun q =>
  ∫ θ in (0 : ℝ)..Real.pi,
    ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)

private def coefTarget {P : Type} (E : ℝ × ℝ × P → ℂ) (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) : ℝ × P → ℂ :=
  fun q => modeE E k q - modeFam Φ k q

private theorem contDiff_modeE {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (k : ℕ) (hk : 2 ≤ k) : ContDiff ℝ (⊤ : ℕ∞) (modeE E k) := by
  have hcast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  have h := hEmode (k - 2)
  rw [hcast] at h
  exact h

private theorem modeE_eq_zero_of_notMem {P : Type} (E : ℝ × ℝ × P → ℂ) {K : Set (ℝ × P)}
    (hEK : ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0) (k : ℕ) {q : ℝ × P} (hq : q ∉ K) :
    modeE E k q = 0 := by
  have h0 : ∀ θ : ℝ, E (q.1, θ, q.2) = 0 := fun θ => hEK q.1 θ q.2 hq
  simp [modeE, h0]

private theorem hasCompactSupport_modeE {P : Type} [NormedAddCommGroup P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (k : ℕ) : HasCompactSupport (modeE E k) := by
  obtain ⟨K, hK, -, hEK⟩ := hEc
  exact HasCompactSupport.intro hK fun q hq => modeE_eq_zero_of_notMem E hEK k hq

private theorem tsupport_modeE_subset {P : Type} [NormedAddCommGroup P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (k : ℕ) : tsupport (modeE E k) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
  obtain ⟨K, hK, hKsub, hEK⟩ := hEc
  have hsupp : Function.support (modeE E k) ⊆ K := by
    intro q hq
    by_contra hqK
    exact Function.mem_support.1 hq (modeE_eq_zero_of_notMem E hEK k hqK)
  exact (closure_minimal hsupp hK.isClosed).trans hKsub

private theorem modeE_eq_zero_of_nonpos {P : Type} [NormedAddCommGroup P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (k : ℕ) {r : ℝ} (hr : r ≤ 0) (p : P) : modeE E k (r, p) = 0 := by
  obtain ⟨K, -, hKsub, hEK⟩ := hEc
  have hnot : ((r, p) : ℝ × P) ∉ K := fun hmem => (not_lt.2 hr) (hKsub hmem).1
  exact modeE_eq_zero_of_notMem E hEK k hnot

private theorem contDiff_modeFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    ContDiff ℝ (⊤ : ℕ∞) (modeFam Φ k) := by
  have hcast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  have h := contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU P Φ hΦ hΦc hΦinv (k - 2)
  rw [hcast] at h
  exact h.1

private theorem hasCompactSupport_modeFam {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    HasCompactSupport (modeFam Φ k) := by
  have hcast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  have h := contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU P Φ hΦ hΦc hΦinv (k - 2)
  rw [hcast] at h
  exact h.2.1

private theorem tsupport_modeFam_subset {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    tsupport (modeFam Φ k) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
  have hcast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  have h := contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU P Φ hΦ hΦc hΦinv (k - 2)
  rw [hcast] at h
  exact h.2.2

private theorem modeFam_eq_zero_of_nonpos {P : Type} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) {r : ℝ} (hr : r ≤ 0)
    (p : P) : modeFam Φ k (r, p) = 0 := by
  have hr' : ¬ 0 < r := not_lt.2 hr
  have h0 : ∀ θ : ℝ, ellipticTransform (entrySlice Φ p) r θ = 0 := fun θ => by simp [ellipticTransform, hr']
  simp [modeFam, h0]

private theorem contDiff_coefTarget {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    ContDiff ℝ (⊤ : ℕ∞) (coefTarget E Φ k) := by
  exact (contDiff_modeE E hEmode k hk).sub (contDiff_modeFam Φ hΦ hΦc hΦinv k hk)

private theorem hasCompactSupport_coefTarget {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    HasCompactSupport (coefTarget E Φ k) := by
  exact (hasCompactSupport_modeE E hEc k).sub (hasCompactSupport_modeFam Φ hΦ hΦc hΦinv k hk)

private theorem coefTarget_eq_zero_of_nonpos {P : Type} [NormedAddCommGroup P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) {r : ℝ} (hr : r ≤ 0) (p : P) : coefTarget E Φ k (r, p) = 0 := by
  show modeE E k (r, p) - modeFam Φ k (r, p) = 0
  rw [modeE_eq_zero_of_nonpos E hEc k hr p, modeFam_eq_zero_of_nonpos Φ k hr p, sub_zero]

private theorem tsupport_coefTarget_subset {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ) (hk : 2 ≤ k) :
    tsupport (coefTarget E Φ k) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
  have hsub : Function.support (coefTarget E Φ k) ⊆
      Function.support (modeE E k) ∪ Function.support (modeFam Φ k) := by
    intro x hx
    by_contra hnot
    have h1 : modeE E k x = 0 := by
      by_contra h
      exact hnot (Set.mem_union_left _ (Function.mem_support.2 h))
    have h2 : modeFam Φ k x = 0 := by
      by_contra h
      exact hnot (Set.mem_union_right _ (Function.mem_support.2 h))
    refine Function.mem_support.1 hx ?_
    show modeE E k x - modeFam Φ k x = 0
    rw [h1, h2, sub_zero]
  calc tsupport (coefTarget E Φ k)
      ⊆ closure (Function.support (modeE E k) ∪ Function.support (modeFam Φ k)) := closure_mono hsub
    _ = tsupport (modeE E k) ∪ tsupport (modeFam Φ k) := closure_union
    _ ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) :=
        Set.union_subset (tsupport_modeE_subset E hEc k) (tsupport_modeFam_subset Φ hΦ hΦc hΦinv k hk)

private theorem exists_window_coefTarget {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (N : ℕ) :
    ∃ r₀ r₁ : ℝ, 0 < r₀ ∧ r₀ ≤ r₁ ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ N → ∀ (r : ℝ) (p : P), (r ≤ r₀ ∨ r₁ ≤ r) → coefTarget E Φ k (r, p) = 0 := by
  obtain ⟨W, hW⟩ : ∃ W : Set (ℝ × P), W = ⋃ k ∈ Finset.Icc 2 N, tsupport (coefTarget E Φ k) := ⟨_, rfl⟩
  have hWc : IsCompact W := by
    rw [hW]
    exact (Finset.Icc 2 N).isCompact_biUnion fun k hk =>
      hasCompactSupport_coefTarget E hEc Φ hΦ hΦc hΦinv k (Finset.mem_Icc.1 hk).1
  have hWsub : W ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
    rw [hW]
    exact Set.iUnion₂_subset fun k hk => tsupport_coefTarget_subset E hEc Φ hΦ hΦc hΦinv k (Finset.mem_Icc.1 hk).1
  have hTc : IsCompact (Prod.fst '' W) := hWc.image continuous_fst
  have hTpos : ∀ x ∈ Prod.fst '' W, 0 < x := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hWsub hw).1
  obtain ⟨m, hm⟩ := (hTc.union (isCompact_singleton (x := (1 : ℝ)))).exists_isLeast
    ⟨1, Set.mem_union_right _ (Set.mem_singleton (1 : ℝ))⟩
  have hmpos : 0 < m := by
    rcases hm.1 with h | h
    · exact hTpos m h
    · rw [Set.mem_singleton_iff.1 h]
      exact one_pos
  obtain ⟨R, hR⟩ := hTc.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨m / 2, max (m / 2) (|R| + 1), half_pos hmpos, le_max_left _ _, fun k hk2 hkN r p hr => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have hrT : r ∈ Prod.fst '' W := by
    refine ⟨(r, p), ?_, rfl⟩
    rw [hW]
    exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨hk2, hkN⟩, hmem⟩
  rcases hr with hr | hr
  · have h1 : m ≤ r := hm.2 (Set.mem_union_left _ hrT)
    linarith
  · have h1 : ‖r‖ ≤ R := mem_closedBall_zero_iff.1 (hR hrT)
    rw [Real.norm_eq_abs] at h1
    have h2 : |R| + 1 ≤ r := (le_max_right _ _).trans hr
    have h3 : r ≤ |r| := le_abs_self r
    have h4 : R ≤ |R| := le_abs_self R
    linarith

private theorem coefTarget_eq_pairing_sub {P : Type} (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) (p : P) {r : ℝ} (hr : 0 < r)
    (hsplit : ∀ a₁ a₂ : ℝ, a₁ * a₂ ≠ 0 → splitTransform (entrySlice Φ p) a₁ a₂ = H (a₁, a₂, p)) :
    coefTarget E Φ k (r, p) =
      discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r - pairingE k Φ p r := by
  have h1 : ∀ t : ℝ, splitTransform (entrySlice Φ p) (r * Real.exp t) (r * Real.exp (-t)) =
      H (r * Real.exp t, r * Real.exp (-t), p) := fun t => hsplit _ _ (by positivity)
  have h2 : ∀ t : ℝ, splitTransform (entrySlice Φ p) (-(r * Real.exp t)) (-(r * Real.exp (-t))) =
      H (-(r * Real.exp t), -(r * Real.exp (-t)), p) := fun t => hsplit _ _ (by rw [neg_mul_neg]; positivity)
  simp only [coefTarget, modeE, modeFam, pairingE, discreteSeriesPairing, h1, h2]
  ring

private theorem coefTarget_eq_zero_of_pairings {P : Type} (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (k : ℕ) (p : P) {r : ℝ} (hr : 0 < r)
    (hsplit : ∀ a₁ a₂ : ℝ, a₁ * a₂ ≠ 0 → splitTransform (entrySlice Φ p) a₁ a₂ = H (a₁, a₂, p))
    (hdata : discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r = 0)
    (hpair : pairingE k Φ p r = 0) : coefTarget E Φ k (r, p) = 0 := by
  rw [coefTarget_eq_pairing_sub H E Φ k p hr hsplit, hdata, hpair, sub_zero]

private theorem sum_coefTarget_eq_zero {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (E : ℝ × ℝ × P → ℂ)
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (k : ℕ)
    {n : ℕ} (c : Fin n → ℂ) (q : Fin n → P)
    (hErel : ∀ b : ℝ × ℝ, 0 < b.1 → 0 < b.2 → b.2 < Real.pi → ∑ j, c j * E (b.1, b.2, q j) = 0)
    (hΦrel : ∀ (r θ : ℝ), ∑ j, c j * ellipticTransform (entrySlice Φ (q j)) r θ = 0) (r : ℝ) :
    ∑ j, c j * coefTarget E Φ k (r, q j) = 0 := by
  by_cases hr : 0 < r
  ·
    have hU : Continuous fun θ : ℝ => (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((Chebyshev.U ℝ ((k : ℤ) - 2)).continuous.comp Real.continuous_cos)

    have hE : ∑ j, c j * modeE E k (r, q j) = 0 := by
      have hint : ∀ j : Fin n, IntervalIntegrable (fun θ : ℝ =>
          c j * (E (r, θ, q j) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) volume 0 Real.pi :=
        fun j => ((hEi r (q j)).mul_continuousOn hU.continuousOn).const_mul (c j)
      have hpull : ∀ j : Fin n, c j * modeE E k (r, q j) = ∫ θ in (0 : ℝ)..Real.pi,
          c j * (E (r, θ, q j) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
        fun j => (intervalIntegral.integral_const_mul (c j) _).symm
      have hsum : ∫ θ in (0 : ℝ)..Real.pi, ∑ j, c j * (E (r, θ, q j) *
            (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          ∑ j, ∫ θ in (0 : ℝ)..Real.pi,
            c j * (E (r, θ, q j) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
        intervalIntegral.integral_finsetSum fun j _ => hint j
      have hzero : Set.EqOn (fun θ : ℝ => ∑ j, c j * (E (r, θ, q j) *
            (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) (fun _ => (0 : ℂ))
          (Set.Ioo 0 Real.pi) := by
        intro θ hθ
        have hrel : ∑ j, c j * E (r, θ, q j) = 0 := hErel (r, θ) hr hθ.1 hθ.2
        calc ∑ j, c j * (E (r, θ, q j) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
            = (∑ j, c j * E (r, θ, q j)) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by rw [hrel, zero_mul]
      calc ∑ j, c j * modeE E k (r, q j)
          = ∑ j, ∫ θ in (0 : ℝ)..Real.pi,
              c j * (E (r, θ, q j) * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
            Finset.sum_congr rfl fun j _ => hpull j
        _ = ∫ θ in (0 : ℝ)..Real.pi, ∑ j, c j * (E (r, θ, q j) *
              (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := hsum.symm
        _ = 0 := by
            rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
              setIntegral_congr_fun measurableSet_Ioo hzero]
            simp

    have hF : ∑ j, c j * modeFam Φ k (r, q j) = 0 := by
      obtain ⟨hcont, hbound⟩ :=
        ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin P Φ hΦ.continuous hΦc hΦinv
      obtain ⟨K₀, hK₀⟩ := hbound {r} isCompact_singleton (Set.singleton_subset_iff.2 hr)
      have hint : ∀ j : Fin n, IntervalIntegrable (fun θ : ℝ => c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
          (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))) volume 0 Real.pi := by
        intro j
        have hA : ContinuousOn (fun θ : ℝ => ellipticTransform (entrySlice Φ (q j)) r θ) (Set.Ioo 0 Real.pi) := by
          have hmap : Set.MapsTo (fun θ : ℝ => ((r, θ, q j) : ℝ × ℝ × P)) (Set.Ioo 0 Real.pi)
              {x : ℝ × ℝ × P | 0 < x.1 ∧ 0 < x.2.1 ∧ x.2.1 < Real.pi} := fun θ hθ => ⟨hr, hθ.1, hθ.2⟩
          have hemb : Continuous fun θ : ℝ => ((r, θ, q j) : ℝ × ℝ × P) := by fun_prop
          exact hcont.comp hemb.continuousOn hmap
        have hAb : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ‖ellipticTransform (entrySlice Φ (q j)) r θ‖ ≤ |K₀| := by
          intro θ hθ
          calc ‖ellipticTransform (entrySlice Φ (q j)) r θ‖ ≤ K₀ * |Real.sin θ| :=
                hK₀ r (Set.mem_singleton r) θ hθ (q j)
            _ ≤ |K₀| * |Real.sin θ| := mul_le_mul_of_nonneg_right (le_abs_self K₀) (abs_nonneg _)
            _ ≤ |K₀| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg _)
            _ = |K₀| := mul_one _
        exact (intervalIntegrable_mul_U_of_bound _ |K₀| hA hAb ((k : ℤ) - 2)).const_mul (c j)
      have hpull : ∀ j : Fin n, c j * modeFam Φ k (r, q j) = ∫ θ in (0 : ℝ)..Real.pi,
          c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
            (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
        fun j => (intervalIntegral.integral_const_mul (c j) _).symm
      have hsum : ∫ θ in (0 : ℝ)..Real.pi, ∑ j, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
            (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          ∑ j, ∫ θ in (0 : ℝ)..Real.pi, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
            (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
        intervalIntegral.integral_finsetSum fun j _ => hint j
      have hzero : ∀ θ : ℝ, ∑ j, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
          (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) = 0 := by
        intro θ
        calc ∑ j, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
              (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ))
            = (∑ j, c j * ellipticTransform (entrySlice Φ (q j)) r θ) *
                (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by rw [hΦrel r θ, zero_mul]
      calc ∑ j, c j * modeFam Φ k (r, q j)
          = ∑ j, ∫ θ in (0 : ℝ)..Real.pi, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
              (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) :=
            Finset.sum_congr rfl fun j _ => hpull j
        _ = ∫ θ in (0 : ℝ)..Real.pi, ∑ j, c j * (ellipticTransform (entrySlice Φ (q j)) r θ *
              (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) := hsum.symm
        _ = 0 := by simp only [hzero, intervalIntegral.integral_zero]
    calc ∑ j, c j * coefTarget E Φ k (r, q j)
        = ∑ j, (c j * modeE E k (r, q j) - c j * modeFam Φ k (r, q j)) :=
          Finset.sum_congr rfl fun j _ => by
            show c j * (modeE E k (r, q j) - modeFam Φ k (r, q j)) = _
            ring
      _ = (∑ j, c j * modeE E k (r, q j)) - ∑ j, c j * modeFam Φ k (r, q j) := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hE, hF, sub_zero]
  · have hr' : r ≤ 0 := not_lt.1 hr
    exact Finset.sum_eq_zero fun j _ => by rw [coefTarget_eq_zero_of_nonpos E hEc Φ k hr' (q j), mul_zero]

private theorem sum_mul_ellipticTransform_entrySlice_eq_zero {P : Type} [NormedAddCommGroup P]
    (L : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hL : Continuous L) (hLc : HasCompactSupport L) {n : ℕ} (c : Fin n → ℂ)
    (q : Fin n → P) (hrel : ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * L (M, q j) = 0) (r θ : ℝ) :
    ∑ j, c j * ellipticTransform (entrySlice L (q j)) r θ = 0 := by

  have hcont : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      Continuous (unitFamily fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j)) := fun j _ => by
    show Continuous fun x : (Fin 2 → Fin 2 → ℝ) × Unit => c j * L (x.1, q j)
    exact continuous_const.mul (hL.comp (continuous_fst.prodMk continuous_const))
  have hsupp : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasCompactSupport (unitFamily fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j)) := fun j _ => by
    have hslice : HasCompactSupport fun M : Fin 2 → Fin 2 → ℝ => L (M, q j) :=
      HasCompactSupport.of_support_subset_isCompact (hLc.isCompact.image continuous_fst) fun M hM =>
        ⟨(M, q j), subset_tsupport _ hM, rfl⟩
    have hmul : HasCompactSupport fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j) := hslice.mul_left
    exact hasCompactSupport_unitFamily hmul
  have hsum := ellipticTransform_entrySlice_sum Finset.univ
    (fun j => unitFamily fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j)) hcont hsupp () r θ

  have hzero : (∑ j, unitFamily fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j)) =
      (0 : (Fin 2 → Fin 2 → ℝ) × Unit → ℂ) := by
    funext x
    simp only [Finset.sum_apply, unitFamily, Pi.zero_apply]
    exact hrel x.1
  rw [hzero, ellipticTransform_entrySlice_zero] at hsum
  have hterm : ∀ j : Fin n, ellipticTransform (entrySlice (unitFamily fun M : Fin 2 → Fin 2 → ℝ =>
      c j * L (M, q j)) ()) r θ = c j * ellipticTransform (entrySlice L (q j)) r θ := by
    intro j
    have hs : entrySlice (unitFamily fun M : Fin 2 → Fin 2 → ℝ => c j * L (M, q j)) () =
        entrySlice (c j • L) (q j) := by
      funext g
      rfl
    rw [hs, ellipticTransform_entrySlice_smul]
  rw [Finset.sum_congr rfl fun j _ => hterm j] at hsum
  exact hsum.symm

private theorem main
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p))
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (hEcont : ContinuousOn E {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi})
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (hvanish : ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r = 0) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ a : ℝ × ℝ, ∑ j, c j * H (a.1, a.2, q j) = 0) →
          (∀ b : ℝ × ℝ, 0 < b.1 → 0 < b.2 → b.2 < Real.pi → ∑ j, c j * E (b.1, b.2, q j) = 0) →
            ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (M, q j) = 0) ∧
      (∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice F p) a₁ a₂ = H (a₁, a₂, p)) ∧
      (∀ (p : P) (r θ : ℝ), 0 < r → 0 < θ → θ < Real.pi →
        ellipticTransform (entrySlice F p) r θ = E (r, θ, p)) := by
  obtain ⟨N, hN⟩ := hvanish

  obtain ⟨hL₀, hL₀c, hL₀inv, hL₀t, -⟩ := dataLift0_props H hH hHc hHsupp hHsym
  obtain ⟨hL₁, hL₁c, hL₁inv, hL₁t, -⟩ := dataLift1_props H hH hHc hHsupp hHsym
  have hL : ContDiff ℝ (⊤ : ℕ∞) (dataLift H) := contDiff_dataLift H hH hHc hHsupp hHsym
  have hLc : HasCompactSupport (dataLift H) := hasCompactSupport_dataLift H hH hHc hHsupp hHsym
  have hLinv : tsupport (dataLift H) ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} :=
    tsupport_dataLift H hH hHc hHsupp hHsym
  have hLsplit : ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
      splitTransform (entrySlice (dataLift0 H + dataLift1 H) p) a₁ a₂ = H (a₁, a₂, p) :=
    fun p a₁ a₂ h => splitTransform_dataLift H hH hHc hHsupp hHsym p h
  have hLpair : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r → pairingE j (dataLift0 H + dataLift1 H) p r = 0 :=
    fun j hj p r hr => pairingE_dataLift H hH hHc hHsupp hHsym hj p hr

  obtain ⟨r₀, r₁, hr₀, hr₀₁, hT0⟩ := exists_window_coefTarget E hEc (dataLift H) hL hLc hLinv N
  obtain ⟨ψ, φs, δ, Δ, εs, hP, hψ1, hφ0, hε, hφpos⟩ :=
    exists_gear (r₀ ^ 2) (r₁ ^ 2) (pow_pos hr₀ 2) (pow_le_pow_left₀ hr₀.le hr₀₁ 2)
  have he : ∀ k : ℕ, 2 ≤ k → k ≤ N → entryFun φs k k ≠ 0 := fun k hk _ =>
    entryFun_diag_ne_zero φs εs k hk (hP k).hφ.continuous (hφ0 k) (hε k (le_trans one_le_two hk)) (hP k).hφε
      (hφpos k)
  have hW : Pieces (dataLift0 H) (dataLift1 H) ψ φs δ Δ εs N (coefTarget E (dataLift H)) r₀ r₁ :=
    { hL₀ := hL₀, hL₀c := hL₀c, hL₀inv := hL₀inv, hL₁ := hL₁, hL₁c := hL₁c, hL₁inv := hL₁inv, hP := hP,
      hT := fun j hj => contDiff_coefTarget E hEmode (dataLift H) hL hLc hLinv j hj,
      hTc := fun j hj => hasCompactSupport_coefTarget E hEc (dataLift H) hL hLc hLinv j hj,
      hr₀ := hr₀, hT0 := hT0, he := he, hψ1 := hψ1 }

  have hc7 : ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
      splitTransform (entrySlice (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) p) a₁ a₂ =
        H (a₁, a₂, p) :=
    fun p a₁ a₂ h => splitTransform_witness hW H hLsplit p h
  have hmode : ∀ j : ℕ, 2 ≤ j → ∀ (p : P) (r : ℝ), 0 < r →
      (∫ θ in (0 : ℝ)..Real.pi, E (r, θ, p) * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) -
          (∫ θ in (0 : ℝ)..Real.pi,
            ellipticTransform (entrySlice (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) p)
              r θ * (((Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
        discreteSeriesPairing j (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r -
          pairingE j (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) p r := by
    intro j _ p r hr
    have h := coefTarget_eq_pairing_sub H E
      (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) j p hr (hc7 p)
    simp only [coefTarget, modeE, modeFam] at h
    exact h
  have hTD : ∀ j : ℕ, 2 ≤ j → j ≤ N → ∀ (p : P) (r : ℝ), 0 < r → coefTarget E (dataLift H) j (r, p) =
      discreteSeriesPairing j (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r := by
    intro j hj _ p r hr
    have h := coefTarget_eq_pairing_sub H E (dataLift H) j p hr fun a₁ a₂ ha =>
      splitTransform_dataLift H hH hHc hHsupp hHsym p ha
    rw [pairingE_dataLift H hH hHc hHsupp hHsym hj p hr, sub_zero] at h
    exact h
  refine ⟨witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H)), contDiff_witness hW,
    hasCompactSupport_witness hW, tsupport_witness hW, ?_⟩

  have hfin := finiteDimensional_span_translates N (dataLift0 H) (dataLift1 H) 0 1
    (fun k M p => apply_mul_coe_eq 0 (dataLift0 H) hL₀inv hL₀t k M p)
    (fun k M p => apply_mul_coe_eq 1 (dataLift1 H) hL₁inv hL₁t k M p)
    (fun i => coefOfSq (coefVec N (entryFun φs) (coefTarget E (dataLift H)) i) i)
    (fun i M => unitFamily (memberE ψ (φs i) i) (M, ())) (fun i M => memberCorr ψ (φs i) i (M, ()))
    (fun i => ((i : ℕ) : ℤ)) (fun i => (((i : ℕ) % 2 : ℕ) : ℤ))
    (fun i k M => apply_mul_coe_eq ((i : ℕ) : ℤ) (unitFamily (memberE ψ (φs i) i))
      (tsupport_unitFamily (tsupport_memberE (hP i) i)) (member_type ψ (φs i) i) k M ())
    (fun i k M => apply_mul_coe_eq (((i : ℕ) % 2 : ℕ) : ℤ) (memberCorr ψ (φs i) i) (memberCorr_props (hP i) i).2.2.1
      (memberCorr_props (hP i) i).2.2.2.1 k M ())
    (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) fun _ => rfl
  refine ⟨hfin.1, hfin.2, ?_, hc7, fun p r θ hr hθ0 hθπ => ?_⟩
  ·
    intro n c q hHrel hErel M
    have hrelL : ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * dataLift H (M, q j) = 0 :=
      sum_mul_dataLift_eq_zero H hH hHc hHsupp hHsym c q hHrel
    have hΦrel : ∀ r θ : ℝ, ∑ j, c j * ellipticTransform (entrySlice (dataLift H) (q j)) r θ = 0 :=
      sum_mul_ellipticTransform_entrySlice_eq_zero (dataLift H) hL.continuous hLc c q hrelL
    have hTrel : ∀ (i : Fin (N + 1)) (r : ℝ), ∑ j, c j * targetVec N (coefTarget E (dataLift H)) (r, q j) i = 0 := by
      intro i r
      by_cases hi : 2 ≤ (i : ℕ)
      · simp only [targetVec, if_pos hi]
        exact sum_coefTarget_eq_zero E hEc hEi (dataLift H) hL hLc hLinv i c q hErel hΦrel r
      · simp only [targetVec, if_neg hi, mul_zero, Finset.sum_const_zero]
    refine relation_witness (witness (dataLift0 H) (dataLift1 H) ψ φs N (coefTarget E (dataLift H))) (dataLift H)
      (fun i => coefOfSq (coefVec N (entryFun φs) (coefTarget E (dataLift H)) i) i)
      (fun i M => unitFamily (memberE ψ (φs i) i) (M, ())) (fun i M => memberCorr ψ (φs i) i (M, ())) (fun _ => rfl)
      c q hrelL (fun k d => ?_) M
    rw [coefVec_eq_sum]
    exact relation_coefOfSq (fun i => (padMatrix N (entryFun φs))⁻¹ k i)
      (fun i x => targetVec N (coefTarget E (dataLift H)) x i) k c q hTrel d
  ·
    exact ellipticTransform_witness hW E hEi hEcont p hr (fun j hj => mode_witness hW hLpair E
      (fun j p r => discreteSeriesPairing j (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r) hmode hTD
      (fun p j hj r hr => hN p j hj r hr) hj p hr) hθ0 hθπ

end BiFiniteSynthesis

end

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p))
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (hEcont : ContinuousOn E {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi})
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (hvanish : ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r = 0) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ a : ℝ × ℝ, ∑ j, c j * H (a.1, a.2, q j) = 0) →
          (∀ b : ℝ × ℝ, 0 < b.1 → 0 < b.2 → b.2 < Real.pi → ∑ j, c j * E (b.1, b.2, q j) = 0) →
            ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (M, q j) = 0) ∧
      (∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice F p) a₁ a₂ = H (a₁, a₂, p)) ∧
      (∀ (p : P) (r θ : ℝ), 0 < r → 0 < θ → θ < Real.pi →
        ellipticTransform (entrySlice F p) r θ = E (r, θ, p)) := by
  exact BiFiniteSynthesis.main P H E hH hHc hHsupp hHsym hEc hEi hEcont hEmode hvanish

end S_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing (solution)
