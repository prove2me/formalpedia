-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
-- name    : GroundTheory_AutomorphicForms_HilbertSchmidtKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:03.956518+00:00
-- url     : https://prove2.me/theorems/df182b0b-ebaf-4dba-8c99-469b06b1cc06
-- title:
--   Hilbert Schmidt Kernel
-- statement:
--   Definitions and structural lemmas for Hilbert Schmidt Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.L2Kernel
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
section SlopeTestRemainingChoices
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    (g : α → E) : eLpNorm g 2 μ ^ 2 = ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]
theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h
end SlopeTestRemainingChoices
variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]
section Kernel
def kernelFun (k : X × Y → 𝕜) (f : Y → 𝕜) (x : X) : 𝕜 := ∫ y, k (x, y) * f y ∂ν
variable (k : Lp 𝕜 2 (μ.prod ν))
theorem measurable_rowSq :
    Measurable fun x => ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν :=
  ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).lintegral_prod_right'
theorem lintegral_rowSq : ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ = ‖k‖ₑ ^ 2 := by
  rw [← lintegral_prod _ ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).aemeasurable,
    Lp.enorm_def, eLpNorm_two_sq]
theorem ae_rowSq_lt_top : ∀ᵐ x ∂μ, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞ := by
  refine ae_lt_top (measurable_rowSq k) ?_
  rw [lintegral_rowSq]
  exact (ENNReal.pow_lt_top enorm_lt_top).ne
theorem enorm_Lp_sq (f : Lp 𝕜 2 ν) : ‖f‖ₑ ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_two_sq]
theorem measurable_row (x : X) : Measurable fun y => k (x, y) :=
  (Lp.stronglyMeasurable k).measurable.comp measurable_prodMk_left
theorem lintegral_row_mul_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    (∫⁻ y, ‖k (x, y) * f y‖ₑ ∂ν) ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 := by
  simp only [enorm_mul]
  rw [enorm_Lp_sq]
  exact lintegral_mul_sq_le ν (measurable_row k x).enorm.aemeasurable
    (Lp.aestronglyMeasurable f).enorm
theorem enorm_kernelFun_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 :=
  (pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2).trans
    (lintegral_row_mul_sq_le k x f)
theorem aestronglyMeasurable_kernelFun (f : Lp 𝕜 2 ν) :
    AEStronglyMeasurable (kernelFun (ν := ν) k f) μ :=
  ((Lp.aestronglyMeasurable k).mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
theorem lintegral_kernelFun_sq_le (f : Lp 𝕜 2 ν) :
    ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ ≤ ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
  calc ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => enorm_kernelFun_sq_le k x f
    _ = ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ (measurable_rowSq k), lintegral_rowSq]
theorem memLp_kernelFun (f : Lp 𝕜 2 ν) : MemLp (kernelFun (ν := ν) k f) 2 μ := by
  refine ⟨aestronglyMeasurable_kernelFun k f, lt_top_of_sq_lt_top ?_⟩
  rw [eLpNorm_two_sq]
  exact (lintegral_kernelFun_sq_le k f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) (ENNReal.pow_lt_top enorm_lt_top))
theorem ae_integrable_row_mul :
    ∀ᵐ x ∂μ, ∀ f : Lp 𝕜 2 ν, Integrable (fun y => k (x, y) * f y) ν := by
  filter_upwards [ae_rowSq_lt_top k] with x hx f
  refine ⟨(measurable_row k x).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f), ?_⟩
  refine lt_top_of_sq_lt_top ((lintegral_row_mul_sq_le k x f).trans_lt ?_)
  exact ENNReal.mul_lt_top hx (ENNReal.pow_lt_top enorm_lt_top)
def kernelOpₗ : Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun f := (memLp_kernelFun k f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (f + g)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      (memLp_kernelFun k g).coeFn_toLp,
      Lp.coeFn_add ((memLp_kernelFun k f).toLp _) ((memLp_kernelFun k g).toLp _),
      ae_integrable_row_mul k] with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, kernelFun, kernelFun, kernelFun,
      ← integral_add (h5 f) (h5 g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (c • f)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_kernelFun k f).toLp _)] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, kernelFun, kernelFun, smul_eq_mul,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]
theorem kernelOpₗ_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOpₗ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  (memLp_kernelFun k f).coeFn_toLp
theorem enorm_kernelOpₗ_sq (f : Lp 𝕜 2 ν) :
    ‖kernelOpₗ k f‖ₑ ^ 2 = ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (kernelOpₗ_apply_ae k f), eLpNorm_two_sq]
  rfl
theorem norm_kernelOpₗ_le (f : Lp 𝕜 2 ν) : ‖kernelOpₗ k f‖ ≤ ‖k‖ * ‖f‖ := by
  have h : ‖kernelOpₗ k f‖ₑ ^ 2 ≤ (‖k‖ₑ * ‖f‖ₑ) ^ 2 := by
    rw [enorm_kernelOpₗ_sq, mul_pow]
    exact lintegral_kernelFun_sq_le k f
  rw [ENNReal.pow_le_pow_left_iff two_ne_zero, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h
def kernelOp : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  (kernelOpₗ k).mkContinuous ‖k‖ (norm_kernelOpₗ_le k)
end Kernel
end
end GroundTheory.Automorphic.L2Kernel


