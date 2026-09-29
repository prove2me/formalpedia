-- Prove2me | solution 1 for AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/95bdff94-b6e6-56dd-972f-30f0fb7ed9be

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Theorems.Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_GL2Twisted_unitaryAverage_translate
import Theorems.Thm_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology AutomorphicForm AutomorphicForm.GL2Twisted
open scoped ContDiff

noncomputable section

namespace P2mHCScalarC

abbrev Ent : Type := Fin 2 → Fin 2 → ℂ

theorem entry_norm_le_norm (Y : Ent) (i j : Fin 2) : ‖Y i j‖ ≤ ‖Y‖ :=
  (norm_le_pi_norm (Y i) j).trans (norm_le_pi_norm Y i)

theorem norm_le_of_entries (Y : Ent) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i j, ‖Y i j‖ ≤ B) : ‖Y‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).2 fun i => (pi_norm_le_iff_of_nonneg hB).2 fun j => h i j

section Chart

abbrev Box : Type := ℝ × ℝ × ℝ × ℝ

def kMat (b : Box) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (b.1 * Complex.I) * (Real.cos b.2.1 * Complex.exp (b.2.2.1 * Complex.I)),
      Complex.exp (b.1 * Complex.I) * (Real.sin b.2.1 * Complex.exp (b.2.2.2 * Complex.I));
    Complex.exp (b.1 * Complex.I) * (-(Real.sin b.2.1 * Complex.exp (-(b.2.2.2 * Complex.I)))),
      Complex.exp (b.1 * Complex.I) * (Real.cos b.2.1 * Complex.exp (-(b.2.2.1 * Complex.I)))]

def kInv (b : Box) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(b.1 * Complex.I)) * (Real.cos b.2.1 * Complex.exp (-(b.2.2.1 * Complex.I))),
      Complex.exp (-(b.1 * Complex.I)) * (-(Real.sin b.2.1 * Complex.exp (b.2.2.2 * Complex.I)));
    Complex.exp (-(b.1 * Complex.I)) * (Real.sin b.2.1 * Complex.exp (-(b.2.2.2 * Complex.I))),
      Complex.exp (-(b.1 * Complex.I)) * (Real.cos b.2.1 * Complex.exp (b.2.2.1 * Complex.I))]

theorem exp_mul_exp_neg (t : ℝ) : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem cos_sq_add_sin_sq' (η : ℝ) : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq η

theorem kInv_mul_kMat (b : Box) : kInv b * kMat b = 1 := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kInv, kMat, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

theorem kMat_mul_kInv (b : Box) : kMat b * kInv b = 1 := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kMat, kInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

theorem norm_exp_real_mul_I (t : ℝ) : ‖Complex.exp (t * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem norm_exp_neg_real_mul_I (t : ℝ) : ‖Complex.exp (-(t * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem kMat_entry_norm_le (b : Box) (i j : Fin 2) : ‖kMat b i j‖ ≤ 1 := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul,
      mul_one] <;>
    assumption

theorem kInv_entry_norm_le (b : Box) (i j : Fin 2) : ‖kInv b i j‖ ≤ 1 := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kInv, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul,
      mul_one] <;>
    assumption

def unitaryAt (b : Box) : GL (Fin 2) ℂ := unitaryElt b.1 b.2.1 b.2.2.1 b.2.2.2

theorem unitaryAt_val (b : Box) : ((unitaryAt b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kMat b := rfl

theorem unitaryAt_inv_val (b : Box) : (((unitaryAt b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kInv b := by
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [unitaryAt_val]
  exact kInv_mul_kMat b

def chartData (b : Box) : Ent × Ent := (Matrix.of.symm (kInv b), Matrix.of.symm (kMat b))

theorem continuous_chartData : Continuous chartData := by
  have hexp : Continuous fun z : ℂ => Complex.exp z := Complex.continuous_exp
  refine Continuous.prodMk ?_ ?_ <;>
    refine continuous_pi fun i => continuous_pi fun j => ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp only [kInv, kMat, Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    fun_prop

theorem chartData_mem (b : Box) : chartData b ∈ Metric.closedBall (0 : Ent × Ent) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (norm_le_of_entries _ zero_le_one (kInv_entry_norm_le b))
    (norm_le_of_entries _ zero_le_one (kMat_entry_norm_le b))

def boxMeasure₃ : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
    ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))

def boxMeasure₂ : Measure (ℝ × ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))).prod boxMeasure₃

def boxMeasure : Measure Box := ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod boxMeasure₂

scoped instance : IsFiniteMeasure boxMeasure₃ := by unfold boxMeasure₃; infer_instance
scoped instance : IsFiniteMeasure boxMeasure₂ := by unfold boxMeasure₂; infer_instance
scoped instance : IsFiniteMeasure boxMeasure := by unfold boxMeasure; infer_instance

theorem integrable_of_continuous_of_bounded {α : Type} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

theorem boxMeasure_integral_eq (g : Box → ℂ) (hg : Continuous g) (M : ℝ) (hM : ∀ b, ‖g b‖ ≤ M) :
    ∫ b, g b ∂boxMeasure =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), g (ψ, η, ξ₁, ξ₂) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  simp only [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le hπ2]
  have h₁ : Integrable g boxMeasure := integrable_of_continuous_of_bounded boxMeasure g hg M hM
  unfold boxMeasure at h₁ ⊢
  rw [integral_prod _ h₁]
  congr 1
  funext ψ
  have h₂ : Integrable (fun y => g (ψ, y)) boxMeasure₂ :=
    integrable_of_continuous_of_bounded boxMeasure₂ _ (hg.comp (continuous_const.prodMk continuous_id)) M
      fun y => hM _
  unfold boxMeasure₂ at h₂ ⊢
  rw [integral_prod _ h₂]
  congr 1
  funext η
  have h₃ : Integrable (fun y => g (ψ, η, y)) boxMeasure₃ :=
    integrable_of_continuous_of_bounded boxMeasure₃ _
      (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) M fun y => hM _
  unfold boxMeasure₃ at h₃ ⊢
  rw [integral_prod _ h₃]

def wt (b : Box) : ℝ := Real.sin b.2.1 * Real.cos b.2.1

theorem continuous_wt : Continuous wt := by unfold wt; fun_prop

theorem norm_wt_le (b : Box) : ‖wt b‖ ≤ 1 := by
  rw [wt, Real.norm_eq_abs, abs_mul]
  calc |Real.sin b.2.1| * |Real.cos b.2.1| ≤ 1 * 1 := by
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
    _ = 1 := one_mul _

theorem integral_sin_mul_cos_complex :
    ∫ η in (0 : ℝ)..(Real.pi / 2), (Real.sin η : ℂ) * (Real.cos η : ℂ) = 1 / 2 := by
  have : (fun η : ℝ => (Real.sin η : ℂ) * (Real.cos η : ℂ)) = fun η : ℝ => ((Real.sin η * Real.cos η : ℝ) : ℂ) := by
    funext η; push_cast; rfl
  rw [this, intervalIntegral.integral_ofReal, integral_sin_mul_cos₁, Real.sin_pi_div_two, Real.sin_zero]
  push_cast
  ring

theorem unitaryAverage_const (z : ℂ) : unitaryAverage (fun _ => z) = z := by
  unfold unitaryAverage
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_smul, intervalIntegral.integral_mul_const,
    smul_mul_assoc, integral_sin_mul_cos_complex, sub_zero]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp
  ring

end Chart

namespace ParamFin

variable {Ω : Type} [TopologicalSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  {X : Ω → M} (hX : Continuous X) {K : Set M} (hK : IsCompact K) (hXK : ∀ t, X t ∈ K)
  {w : Ω → ℝ} (hw : Continuous w) {W : ℝ} (hwW : ∀ t, ‖w t‖ ≤ W)

def dP {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : M × P → E) : M × P → (P →L[ℝ] E) :=
  fun q => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inr ℝ M P)

theorem contDiff_dP {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (dP Ψ) :=
  (contDiff_infty_iff_fderiv.mp hΨ).2.clm_comp contDiff_const

theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : ContDiff ℝ ∞ Ψ) (m : M) (p : P) : HasFDerivAt (fun p => Ψ (m, p)) (dP Ψ (m, p)) p :=
  ((hΨ.differentiable (by simp)) (m, p)).hasFDerivAt.comp p (hasFDerivAt_prodMk_right m p)

include hK hXK hwW in
theorem exists_bound_near {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : M × P → E)
    (hΨ : Continuous Ψ) (p₀ : P) :
    ∃ C : ℝ, ∀ t, ∀ p ∈ Metric.ball p₀ 1, ‖w t • Ψ (X t, p)‖ ≤ W * C := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall p₀ 1)).exists_bound_of_continuousOn hΨ.continuousOn
  refine ⟨max C 0, fun t p hp => ?_⟩
  rw [norm_smul]
  have h1 := hC (X t, p) ⟨hXK t, Metric.ball_subset_closedBall hp⟩
  exact mul_le_mul (hwW t) (h1.trans (le_max_left _ _)) (norm_nonneg _) ((norm_nonneg _).trans (hwW t))

include hX hw in
theorem aestronglyMeasurable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : Continuous Ψ) (p : P) : AEStronglyMeasurable (fun t => w t • Ψ (X t, p)) μ :=
  (hw.smul (hΨ.comp (hX.prodMk continuous_const))).aestronglyMeasurable

include hX hK hXK hw hwW in
theorem integrable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : M × P → E}
    (hΨ : Continuous Ψ) (p : P) : Integrable (fun t => w t • Ψ (X t, p)) μ := by
  obtain ⟨C, hC⟩ := exists_bound_near hK hXK hwW Ψ hΨ p
  exact Integrable.of_bound (aestronglyMeasurable_smul (μ := μ) hX hw hΨ p) (W * C)
    (Filter.Eventually.of_forall fun t => hC t p (Metric.mem_ball_self one_pos))

include hX hK hXK hw hwW in

theorem contDiff_integral_nat (n : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : M × P → E} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ n (fun p => ∫ t, w t • Ψ (X t, p) ∂μ) := by
  induction n generalizing E with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    obtain ⟨C, hC⟩ := exists_bound_near hK hXK hwW Ψ hΨ.continuous p₀
    refine continuousAt_of_dominated (bound := fun _ => W * C) ?_ ?_ (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun p => aestronglyMeasurable_smul (μ := μ) hX hw hΨ.continuous p
    · exact Filter.eventually_of_mem (Metric.ball_mem_nhds p₀ one_pos) fun p hp =>
        Filter.Eventually.of_forall fun t => hC t p hp
    · exact Filter.Eventually.of_forall fun t =>
        ((hΨ.continuous.comp (continuous_const.prodMk continuous_id)).const_smul _).continuousAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ t, w t • dP Ψ (X t, p) ∂μ, ih (contDiff_dP hΨ), fun p₀ => ?_⟩
    obtain ⟨C, hC⟩ := exists_bound_near hK hXK hwW (dP Ψ) (contDiff_dP hΨ).continuous p₀
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
      (F := fun p t => w t • Ψ (X t, p)) (F' := fun p t => w t • dP Ψ (X t, p))
      (bound := fun _ => W * C) (Metric.ball_mem_nhds p₀ one_pos)
      (Filter.Eventually.of_forall fun p => aestronglyMeasurable_smul (μ := μ) hX hw hΨ.continuous p)
      (integrable_smul hX hK hXK hw hwW hΨ.continuous p₀)
      (aestronglyMeasurable_smul (μ := μ) hX hw (contDiff_dP hΨ).continuous p₀)
      (Filter.Eventually.of_forall fun t p hp => hC t p hp)
      (integrable_const _)
      (Filter.Eventually.of_forall fun t p _ => (hasFDerivAt_slice hΨ (X t) p).const_smul (w t))

include hX hK hXK hw hwW in

theorem contDiff_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ψ : M × P → E} (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (fun p => ∫ t, w t • Ψ (X t, p) ∂μ) :=
  contDiff_infty.mpr fun n => contDiff_integral_nat hX hK hXK hw hwW n hΨ

end ParamFin

section Avg

variable (Φ : Ent → ℂ)

def avgConj (E : Ent) : ℂ :=
  unitaryAverage fun k =>
    Φ (Matrix.of.symm (((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of E *
      (k : Matrix (Fin 2) (Fin 2) ℂ)))

def fam (q : (Ent × Ent) × Ent) : ℂ := Φ (Matrix.of.symm (Matrix.of q.1.1 * Matrix.of q.2 * Matrix.of q.1.2))

theorem contDiff_conjMap :
    ContDiff ℝ ∞ (fun q : (Ent × Ent) × Ent => Matrix.of.symm (Matrix.of q.1.1 * Matrix.of q.2 * Matrix.of q.1.2)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  fun_prop

variable {Φ}

theorem contDiff_fam (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ ∞ (fam Φ) := hΦ.comp (contDiff_conjMap)

theorem continuous_fam (hΦ : Continuous Φ) : Continuous (fam Φ) := hΦ.comp (ContDiff.continuous contDiff_conjMap)

theorem integrand_eq_fam (E : Ent) (b : Box) :
    Φ (Matrix.of.symm ((((unitaryAt b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of E *
      ((unitaryAt b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) = fam Φ (chartData b, E) := by
  rw [unitaryAt_inv_val, unitaryAt_val]
  rfl

theorem avgConj_eq_integral (hΦ : Continuous Φ) {M₀ : ℝ} (hM₀ : ∀ E, ‖Φ E‖ ≤ M₀) (E : Ent) :
    avgConj Φ E = (1 / (4 * Real.pi ^ 3) : ℝ) • ∫ b, wt b • fam Φ (chartData b, E) ∂boxMeasure := by
  have hg : Continuous fun b : Box => (wt b : ℂ) * fam Φ (chartData b, E) :=
    (Complex.continuous_ofReal.comp continuous_wt).mul
      ((continuous_fam hΦ).comp (continuous_chartData.prodMk continuous_const))
  have hM : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hgM : ∀ b : Box, ‖(wt b : ℂ) * fam Φ (chartData b, E)‖ ≤ M₀ := by
    intro b
    rw [norm_mul, Complex.norm_real]
    calc ‖wt b‖ * ‖fam Φ (chartData b, E)‖ ≤ 1 * M₀ := by
          gcongr
          · exact norm_wt_le b
          · exact hM₀ _
      _ = M₀ := one_mul _
  have h := boxMeasure_integral_eq _ hg M₀ hgM
  unfold avgConj unitaryAverage
  simp_rw [Complex.real_smul]
  push_cast
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun ψ _ => intervalIntegral.integral_congr fun η _ =>
    intervalIntegral.integral_congr fun ξ₁ _ => intervalIntegral.integral_congr fun ξ₂ _ => ?_
  simp only [wt]
  rw [← integrand_eq_fam]
  push_cast
  rfl

theorem contDiff_avgConj (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {M₀ : ℝ} (hM₀ : ∀ E, ‖Φ E‖ ≤ M₀) :
    ContDiff ℝ (⊤ : ℕ∞) (avgConj Φ) := by
  have h : avgConj Φ = fun E => (1 / (4 * Real.pi ^ 3) : ℝ) • ∫ b, wt b • fam Φ (chartData b, E) ∂boxMeasure :=
    funext fun E => avgConj_eq_integral hΦ.continuous hM₀ E
  rw [h]
  exact (ParamFin.contDiff_integral (μ := boxMeasure) continuous_chartData
    (isCompact_closedBall (0 : Ent × Ent) 1) chartData_mem continuous_wt norm_wt_le (contDiff_fam hΦ)).const_smul
    (1 / (4 * Real.pi ^ 3) : ℝ)

theorem entry_norm_le_of_conj (b : Box) (M : Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ)
    (h : ∀ i j, ‖(kInv b * M * kMat b) i j‖ ≤ B) (i j : Fin 2) : ‖M i j‖ ≤ 4 * B := by
  set X : Matrix (Fin 2) (Fin 2) ℂ := kInv b * M * kMat b with hX
  have hM : M = kMat b * X * kInv b := by
    rw [hX, Matrix.mul_assoc (kInv b), ← Matrix.mul_assoc (kMat b), kMat_mul_kInv, Matrix.one_mul,
      Matrix.mul_assoc, kMat_mul_kInv, Matrix.mul_one]
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0 0)
  have key : ∀ a c : Fin 2, ‖kMat b i a * X a c * kInv b c j‖ ≤ B := by
    intro a c
    rw [norm_mul, norm_mul]
    calc ‖kMat b i a‖ * ‖X a c‖ * ‖kInv b c j‖ ≤ 1 * B * 1 :=
          mul_le_mul (mul_le_mul (kMat_entry_norm_le b i a) (h a c) (norm_nonneg _) zero_le_one)
            (kInv_entry_norm_le b c j) (norm_nonneg _) (by positivity)
      _ = B := by ring
  rw [hM, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul]
  calc ‖kMat b i 0 * X 0 0 * kInv b 0 j + kMat b i 1 * X 1 0 * kInv b 0 j +
          (kMat b i 0 * X 0 1 * kInv b 1 j + kMat b i 1 * X 1 1 * kInv b 1 j)‖
        ≤ ‖kMat b i 0 * X 0 0 * kInv b 0 j‖ + ‖kMat b i 1 * X 1 0 * kInv b 0 j‖ +
          (‖kMat b i 0 * X 0 1 * kInv b 1 j‖ + ‖kMat b i 1 * X 1 1 * kInv b 1 j‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ B + B + (B + B) := by gcongr <;> exact key _ _
    _ = 4 * B := by ring

theorem avgConj_eq_zero_of_forall (E : Ent)
    (h : ∀ b : Box, Φ (Matrix.of.symm ((((unitaryAt b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.of E * ((unitaryAt b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) = 0) :
    avgConj Φ E = 0 := by
  unfold avgConj unitaryAverage
  have h' : ∀ ψ η ξ₁ ξ₂ : ℝ, Φ (Matrix.of.symm ((((unitaryElt ψ η ξ₁ ξ₂)⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of E * ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ))) = 0 := fun ψ η ξ₁ ξ₂ => h (ψ, η, ξ₁, ξ₂)
  simp only [h']
  simp

theorem hasCompactSupport_avgConj (hΦc : HasCompactSupport Φ) : HasCompactSupport (avgConj Φ) := by
  obtain ⟨B, hB⟩ := hΦc.isCompact.isBounded.exists_norm_le
  have hB0 : 0 ≤ 4 * max B 0 := by positivity
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Ent) (4 * max B 0)) fun E hE => ?_
  refine avgConj_eq_zero_of_forall E fun b => ?_
  by_contra hne
  apply hE
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmem := subset_tsupport _ (Function.mem_support.2 hne)
  have hle := hB _ hmem
  rw [unitaryAt_inv_val, unitaryAt_val] at hle
  refine norm_le_of_entries _ hB0 fun i j => ?_
  refine entry_norm_le_of_conj b (Matrix.of E) (max B 0) (fun i' j' => ?_) i j
  exact ((entry_norm_le_norm _ i' j').trans hle).trans (le_max_left _ _)

theorem avgConj_conj_unitary (hΦ : Continuous Φ) (u : Matrix (Fin 2) (Fin 2) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (E : Ent) :
    avgConj Φ (Matrix.of.symm (u * Matrix.of E * star u)) = avgConj Φ E := by
  have h1 : u * star u = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  have h2 : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  set uG : GL (Fin 2) ℂ := ⟨u, star u, h1, h2⟩ with huG
  set F₀ : GL (Fin 2) ℂ → ℂ := fun k =>
    Φ (Matrix.of.symm (((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of E *
      (k : Matrix (Fin 2) (Fin 2) ℂ))) with hF₀
  have hF₀c : Continuous F₀ := by
    refine hΦ.comp ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_symm_apply]
    have hc : Continuous fun k : GL (Fin 2) ℂ => ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of E *
        (k : Matrix (Fin 2) (Fin 2) ℂ) :=
      ((Units.continuous_coe_inv.mul continuous_const).mul Units.continuous_val)
    exact (continuous_apply j).comp ((continuous_apply i).comp hc)
  have h₀ : star (((uG⁻¹ : GL (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * ((uG⁻¹ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    show star (star u) * star u = 1
    rw [star_star, h1]
  have h₁ : star ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      1 := by simp
  have key := AutomorphicForm.GL2Twisted.unitaryAverage_translate F₀ hF₀c uG⁻¹ 1 h₀ h₁
  unfold avgConj
  rw [← key]
  congr 1
  funext k
  simp only [hF₀, mul_one, mul_inv_rev, inv_inv, Units.val_mul]
  congr 1
  show ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (u * Matrix.of E * star u) * (k : Matrix (Fin 2) (Fin 2) ℂ) =
    ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * u * Matrix.of E * (star u * (k : Matrix (Fin 2) (Fin 2) ℂ))
  simp only [Matrix.mul_assoc]

theorem avgConj_scalar (c : ℂ) : avgConj Φ (Matrix.of.symm !![c, 0; 0, c]) = Φ (Matrix.of.symm !![c, 0; 0, c]) := by
  have hsc : (!![c, 0; 0, c] : Matrix (Fin 2) (Fin 2) ℂ) = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  unfold avgConj
  have h : ∀ k : GL (Fin 2) ℂ, ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.of (Matrix.of.symm !![c, 0; 0, c]) * (k : Matrix (Fin 2) (Fin 2) ℂ) = !![c, 0; 0, c] := by
    intro k
    rw [Equiv.apply_symm_apply, hsc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]
  simp_rw [h]
  exact unitaryAverage_const _

end Avg

section FromF

variable {f : GL (Fin 2) ℂ → ℂ} {Φ : Ent → ℂ}
  (hfΦ : ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) (hfc : HasCompactSupport f)

def entries (g : GL (Fin 2) ℂ) : Ent := fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j

theorem continuous_entries : Continuous entries :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)))

def Kf (f : GL (Fin 2) ℂ → ℂ) : Set Ent := entries '' tsupport f

include hfc in
theorem isCompact_Kf : IsCompact (Kf f) := hfc.isCompact.image continuous_entries

omit hfΦ hfc in
theorem det_ne_zero_of_mem_Kf {E : Ent} (hE : E ∈ Kf f) : Matrix.det (Matrix.of E) ≠ 0 := by
  obtain ⟨g, -, rfl⟩ := hE
  show Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero

include hfΦ in
theorem apply_eq_zero_of_det_ne_zero_of_notMem {E : Ent} (hdet : Matrix.det (Matrix.of E) ≠ 0) (hE : E ∉ Kf f) :
    Φ E = 0 := by
  set g : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of E) hdet with hg
  have hval : entries g = E := rfl
  have hfg : f g = Φ E := hfΦ g
  have hg' : g ∉ tsupport f := fun h => hE ⟨g, h, hval⟩
  rw [← hfg]
  exact image_eq_zero_of_notMem_tsupport hg'

include hfΦ hfc in
theorem apply_eq_zero_of_notMem (hΦ : Continuous Φ) {E : Ent} (hE : E ∉ Kf f) : Φ E = 0 := by
  by_cases hdet : Matrix.det (Matrix.of E) ≠ 0
  · exact apply_eq_zero_of_det_ne_zero_of_notMem hfΦ hdet hE
  push Not at hdet

  set Et : ℝ → Ent := fun t => fun i j => E i j + (t : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j with hEt
  have hcont : Continuous Et := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [hEt]
    fun_prop
  have h0 : Et 0 = E := by
    funext i j
    simp [hEt]
  set tr : ℂ := E 0 0 + E 1 1 with htr
  have hdet0 : E 0 0 * E 1 1 - E 0 1 * E 1 0 = 0 := by
    rw [Matrix.det_fin_two] at hdet
    simpa using hdet
  have hdetf : ∀ t : ℝ, Matrix.det (Matrix.of (Et t)) = (t : ℂ) * ((t : ℂ) + tr) := by
    intro t
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, hEt, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, add_zero, htr]
    linear_combination hdet0
  set δ : ℝ := if tr = 0 then 1 else ‖tr‖ with hδ
  have hδpos : 0 < δ := by
    simp only [hδ]
    split_ifs with h
    · exact one_pos
    · exact norm_pos_iff.2 h
  have hne : ∀ t : ℝ, 0 < t → t < δ → Matrix.det (Matrix.of (Et t)) ≠ 0 := by
    intro t ht htδ
    rw [hdetf]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 ht.ne') fun h => ?_
    have htr' : tr = -(t : ℂ) := by linear_combination h
    by_cases h0 : tr = 0
    · rw [h0] at htr'
      have : (t : ℂ) = 0 := by linear_combination htr'
      exact ht.ne' (by exact_mod_cast this)
    · have hn : ‖tr‖ = t := by
        rw [htr', norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      simp only [hδ, if_neg h0] at htδ
      linarith
  have hK : IsClosed (Kf f) := (isCompact_Kf hfc).isClosed
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Et t ∉ Kf f := by
    have ht : Tendsto Et (𝓝[>] 0) (𝓝 E) := by
      rw [← h0]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht.eventually (hK.isOpen_compl.mem_nhds hE)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Matrix.det (Matrix.of (Et t)) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht using hne t ht.1 ht.2
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Φ (Et t) = 0 := by
    filter_upwards [hev1, hev2] with t h1 h2 using apply_eq_zero_of_det_ne_zero_of_notMem hfΦ h2 h1
  have hlim : Tendsto (fun t => Φ (Et t)) (𝓝[>] 0) (𝓝 (Φ E)) := by
    rw [← h0]
    exact ((hΦ.comp hcont).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun t => Φ (Et t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique hlim hlim0

include hfΦ hfc in
theorem hasCompactSupport_of_entries (hΦ : Continuous Φ) : HasCompactSupport Φ :=
  HasCompactSupport.intro (isCompact_Kf hfc) fun E hE => apply_eq_zero_of_notMem hfΦ hfc hΦ hE

include hfΦ hfc in
theorem tsupport_subset_Kf (hΦ : Continuous Φ) : tsupport Φ ⊆ Kf f :=
  closure_minimal (fun E hE => by_contra fun h => hE (apply_eq_zero_of_notMem hfΦ hfc hΦ h))
    (isCompact_Kf hfc).isClosed

include hfΦ hfc in
theorem tsupport_subset_isUnit (hΦ : Continuous Φ) : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} :=
  fun E hE => isUnit_iff_ne_zero.2 (det_ne_zero_of_mem_Kf (tsupport_subset_Kf hfΦ hfc hΦ hE))

include hfΦ in
theorem continuous_of_entries (hΦ : Continuous Φ) : Continuous f := by
  have : f = Φ ∘ entries := funext fun g => hfΦ g
  rw [this]
  exact hΦ.comp continuous_entries

end FromF

section Diag

theorem locallyCompactSpace_GL : LocallyCompactSpace (GL (Fin 2) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem det_diag_ne_zero (c : ℂ) (hc : c ≠ 0) (w : ℂ) :
    Matrix.det (!![c * Complex.exp w, 0; 0, c * Complex.exp (-w)]) ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero]
  exact mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) (mul_ne_zero hc (Complex.exp_ne_zero _))

def gam (c : ℂ) (hc : c ≠ 0) (w : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c * Complex.exp w, 0; 0, c * Complex.exp (-w)] (det_diag_ne_zero c hc w)

theorem gam_val (c : ℂ) (hc : c ≠ 0) (w : ℂ) : ((gam c hc w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![c * Complex.exp w, 0; 0, c * Complex.exp (-w)] := rfl

theorem gam_inv_val (c : ℂ) (hc : c ≠ 0) (w : ℂ) : (((gam c hc w)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![c⁻¹ * Complex.exp (-w), 0; 0, c⁻¹ * Complex.exp w] := by
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [gam_val, Matrix.mul_fin_two, Matrix.one_fin_two]
  have h1 : c⁻¹ * Complex.exp (-w) * (c * Complex.exp w) = 1 := by
    rw [show c⁻¹ * Complex.exp (-w) * (c * Complex.exp w) = (c⁻¹ * c) * (Complex.exp (-w) * Complex.exp w) by ring,
      inv_mul_cancel₀ hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  have h2 : c⁻¹ * Complex.exp w * (c * Complex.exp (-w)) = 1 := by
    rw [show c⁻¹ * Complex.exp w * (c * Complex.exp (-w)) = (c⁻¹ * c) * (Complex.exp w * Complex.exp (-w)) by ring,
      inv_mul_cancel₀ hc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  simp [h1, h2]

theorem continuous_gam (c : ℂ) (hc : c ≠ 0) : Continuous (gam c hc) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ gam c hc) = fun w => !![c * Complex.exp w, 0; 0, c * Complex.exp (-w)] := rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun w => (((gam c hc w)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun w => !![c⁻¹ * Complex.exp (-w), 0; 0, c⁻¹ * Complex.exp w] := funext (gam_inv_val c hc)
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem gam_zero (c : ℂ) (hc : c ≠ 0) (cu : ℂˣ) (hcu : (cu : ℂ) = c) : gam c hc 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) cu := by
  refine Units.ext ?_
  rw [gam_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hcu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_gam (c : ℂ) (hc : c ≠ 0) (cu : ℂˣ) (hcu : (cu : ℂ) = c) (w : ℂ) : Matrix.GeneralLinearGroup.det (gam c hc w) = cu ^ 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, gam_val, Matrix.det_fin_two_of, Units.val_pow_eq_pow_val, hcu]
  rw [show c * Complex.exp w * (c * Complex.exp (-w)) - 0 * 0 = c ^ 2 * (Complex.exp w * Complex.exp (-w)) by ring,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

theorem exp_ne_exp_neg (c : ℂ) (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ < 1) : c * Complex.exp w ≠ c * Complex.exp (-w) := by
  intro h
  have h1 : Complex.exp w = Complex.exp (-w) := mul_left_cancel₀ hc h
  have h2 : Complex.exp (2 * w) = 1 := by
    rw [two_mul, Complex.exp_add]
    nth_rewrite 2 [h1]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hw' : w = n * (Real.pi * Complex.I) := by linear_combination hn / 2
  by_cases hn0 : n = 0
  · rw [hn0] at hw'
    simp at hw'
    exact hw hw'
  · have hnorm : ‖w‖ = |(n : ℝ)| * Real.pi := by
      rw [hw', norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn0
    have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith

theorem isRegularSemisimple_gam (c : ℂ) (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ < 1) : IsRegularSemisimple (gam c hc w) := by
  rw [isRegularSemisimple_iff_ne_zero, gam_val, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have hne := exp_ne_exp_neg c hc hw hw1
  intro h
  apply hne
  have : (c * Complex.exp w - c * Complex.exp (-w)) ^ 2 = 0 := by linear_combination h
  exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this)

end Diag

section Main

theorem main
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (f : GL (Fin 2) ℂ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
    (cu : ℂˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) cu),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = cu ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) cu) = 0 := by
  obtain ⟨⟨Φ, hΦs, hfΦ⟩, hfc⟩ := hf
  set c : ℂ := (cu : ℂ) with hc_def
  have hc : c ≠ 0 := cu.ne_zero

  have hΦc : HasCompactSupport Φ := hasCompactSupport_of_entries hfΦ hfc hΦs.continuous
  have hΦU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := tsupport_subset_isUnit hfΦ hfc hΦs.continuous
  have hfcont : Continuous f := continuous_of_entries hfΦ hΦs.continuous
  obtain ⟨M₀, hM₀⟩ := hΦs.continuous.bounded_above_of_compact_support hΦc

  set F : Ent → ℂ := avgConj Φ with hF_def
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_avgConj hΦs hM₀
  have hFc : HasCompactSupport F := hasCompactSupport_avgConj hΦc
  have hFinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ E : Ent, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E :=
    fun u hu E => avgConj_conj_unitary hΦs.continuous u hu E

  obtain ⟨U, hU, hvanU⟩ := hvan
  have hpre : (gam c hc) ⁻¹' U ∈ 𝓝 (0 : ℂ) := by
    have ht := (continuous_gam c hc).tendsto 0
    rw [gam_zero c hc cu rfl] at ht
    exact ht hU
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhds_iff.1 hpre

  have hslice : ∀ w : ℂ, w ≠ 0 → ‖w‖ < min ε₁ 1 →
      ∫ v : ℂ, F (Matrix.of.symm !![c * Complex.exp w, v; 0, c * Complex.exp (-w)]) = 0 := by
    intro w hw hwε
    have hw1 : ‖w‖ < 1 := lt_of_lt_of_le hwε (min_le_right _ _)
    have hwε₁ : ‖w‖ < ε₁ := lt_of_lt_of_le hwε (min_le_left _ _)
    set a₁ : ℂ := c * Complex.exp w with ha₁_def
    set a₂ : ℂ := c * Complex.exp (-w) with ha₂_def
    have ha₁ : a₁ ≠ 0 := mul_ne_zero hc (Complex.exp_ne_zero _)
    have ha₂ : a₂ ≠ 0 := mul_ne_zero hc (Complex.exp_ne_zero _)
    have hne : a₁ ≠ a₂ := exp_ne_exp_neg c hc hw hw1
    set γ : GL (Fin 2) ℂ := gam c hc w with hγ_def
    have hγU : γ ∈ U := hball (by rwa [Metric.mem_ball, dist_zero_right])
    have hγdet : Matrix.GeneralLinearGroup.det γ = cu ^ 2 := det_gam c hc cu rfl w
    have hγreg : IsRegularSemisimple γ := isRegularSemisimple_gam c hc hw hw1
    have hγval : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂] := rfl

    letI : MeasurableSpace (GL (Fin 2) ℂ) := glBorelOf ℂ
    haveI : BorelSpace (GL (Fin 2) ℂ) := borelSpace_glBorelOf ℂ
    letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := centralizerBorel ℂ γ
    haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := ⟨rfl⟩
    haveI := locallyCompactSpace_GL
    have hTc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : Set (GL (Fin 2) ℂ)) := by
      change IsClosed (({γ} : Set (GL (Fin 2) ℂ)).centralizer)
      exact Set.isClosed_centralizer _
    haveI : LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) :=
      hTc.isClosedEmbedding_subtypeVal.locallyCompactSpace
    set τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := Measure.haar with hτ_def
    have hτ : Measure.IsHaarMeasure τ := by rw [hτ_def]; infer_instance

    set Φ' : Ent × PUnit → ℂ := fun q => Φ q.1 with hΦ'_def
    have hΦ's : ContDiff ℝ (⊤ : ℕ∞) Φ' := hΦs.comp contDiff_fst
    have hsub : Function.support Φ' ⊆ tsupport Φ ×ˢ (Set.univ : Set PUnit) := fun q hq =>
      ⟨subset_tsupport _ (Function.mem_support.2 hq), Set.mem_univ _⟩
    have hΦ'c : HasCompactSupport Φ' :=
      HasCompactSupport.intro (hΦc.isCompact.prod isCompact_univ) fun q hq =>
        Function.notMem_support.1 fun h => hq (hsub h)
    have hΦ'U : tsupport Φ' ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := fun q hq =>
      hΦU (closure_minimal hsub (hΦc.isCompact.prod isCompact_univ).isClosed hq).1
    obtain ⟨g, -, -, hg⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple ℂ PUnit
        μ hμ γ hγreg τ hτ Φ' hΦ's hΦ'c hΦ'U
    have hex : IsOrbitalIntegralOn ℂ μ γ τ f (g PUnit.unit) := by
      have hfeq : f = fun x : GL (Fin 2) ℂ => Φ' (Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) ℂ), PUnit.unit) :=
        funext fun x => hfΦ x
      rw [hfeq]
      exact (hg PUnit.unit).1
    have hI0 : g PUnit.unit = 0 := hvanU γ hγU hγdet hγreg τ hτ _ hex

    obtain ⟨κ, hκ, hbridge⟩ :=
      AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage μ hμ a₁ a₂
        ha₁ ha₂ hne γ hγval τ hτ
    have e := hbridge f hfcont hfc _ hex
    rw [hI0] at e
    have hint0 : ∫ v : ℂ, unitaryAverage (fun k =>
        if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
          f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) = 0 := by
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      exact (mul_eq_zero.1 e.symm).resolve_left hκ'
    have hint_eq : ∀ v : ℂ, unitaryAverage (fun k =>
        if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
          f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) = F (Matrix.of.symm !![a₁, v; 0, a₂]) := by
      intro v
      have hdet : Matrix.det !![a₁, v; 0, a₂] ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        simpa using ⟨ha₁, ha₂⟩
      simp only [hF_def, avgConj]
      congr 1
      funext k
      rw [dif_pos hdet, hfΦ]
      rfl
    simp_rw [hint_eq] at hint0
    exact hint0

  have key :=
    AutomorphicForm.apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero F hF hFc
      hFinv c hc ⟨min ε₁ 1, lt_min hε₁ one_pos, hslice⟩
  rw [hF_def, avgConj_scalar] at key
  rw [hfΦ]
  have hsc : (fun i j => ((Matrix.GeneralLinearGroup.scalar (Fin 2) cu : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j) =
      Matrix.of.symm !![c, 0; 0, c] := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [hc_def]
  rw [hsc]
  exact key

end Main

end P2mHCScalarC
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero.P2mHCScalarC"

end
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero.P2mHCScalarC"

open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (f : GL (Fin 2) ℂ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
    (c : ℂˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 :=
  P2mHCScalarC.main μ hμ f hf c hvan

end S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero (solution)
