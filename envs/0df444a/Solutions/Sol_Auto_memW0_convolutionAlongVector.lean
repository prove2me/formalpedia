-- Prove2me | solution 1 for Auto.memW0_convolutionAlongVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:52.181673+00:00
-- url     : https://prove2.me/submissions/f44a1bcb-d621-481c-bb1e-3e8e61538411

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
public import Theorems.Thm_Auto_aux_memW0_integral_real
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearEquiv_between_of_integrable_radius
public import Theorems.Thm_Auto_MemW0_aux_mul_prod
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
namespace Auto
theorem _root_.solution {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {rho : EuclideanSpace ℝ (Fin n) → 𝕜} {phi : ℝ → 𝕜}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha : EuclideanSpace ℝ (Fin n)) :
    MemW0 (convolutionAlongVector rho phi alpha) := by
  let : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
    infer_instance
  let F : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜 := fun xp ↦ rho xp.1 * phi xp.2
  have hF : MemW0 F := by
    simpa [F] using hrho.aux_mul_prod hphi
  have hFs : MemW0 (F ∘ aux_shear alpha) := by
    apply hF.aux_comp_continuousLinearEquiv_between_of_integrable_radius (aux_shear alpha)
    exact aux_integrable_wienerEnvelope_of_integrable' hF.1 zero_lt_one
      (norm_nonneg (aux_shear alpha).toContinuousLinearMap) hF.2
  have hI := aux_memW0_integral_real hFs
  change MemW0 (fun u ↦ ∫ p : ℝ, rho (u - p • alpha) * phi p)
  simpa [F, aux_shear, Function.comp_def] using hI
end Auto
