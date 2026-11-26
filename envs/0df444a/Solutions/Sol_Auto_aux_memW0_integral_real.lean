-- Prove2me | solution 1 for Auto.aux_memW0_integral_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:49.554115+00:00
-- url     : https://prove2.me/submissions/184d9440-4c21-4148-9184-2294b0f1aeec

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
public import Theorems.Thm_Auto_aux_continuous_integral_real
public import Theorems.Thm_Auto_aux_integrable_of_memW0
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice_of_addHaar
public import Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_continuous_wienerEnvelope


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
namespace Auto
theorem _root_.solution {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    MemW0 (fun u ↦ ∫ p, f (u, p)) := by
  let : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
    infer_instance
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := wienerEnvelope f 1
  have hF : MemW0 F := by
    simpa [F] using hf.aux_mem_wienerEnvelope zero_le_one
  have hF_slice (u : EuclideanSpace ℝ (Fin n)) : Integrable (fun p ↦ F (u, p)) :=
    aux_integrable_of_memW0 (hF.aux_memW0_slice_of_addHaar u)
  have hf_slice (u : EuclideanSpace ℝ (Fin n)) : Integrable (fun p ↦ f (u, p)) :=
    aux_integrable_of_memW0 (hf.aux_memW0_slice_of_addHaar u)
  have hcont : Continuous (fun u ↦ ∫ p, f (u, p)) := aux_continuous_integral_real hf
  refine ⟨hcont, ?_⟩
  have hH : Integrable (fun u ↦ ∫ p, F (u, p)) := hf.2.integral_prod_left
  refine hH.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun u ↦ aux_wienerEnvelope_nonneg hcont zero_le_one u)
    (ae_of_all _ fun u ↦ ?_)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨w, hw, rfl⟩
  change ‖∫ p, f (u + w, p)‖ ≤ ∫ p, F (u, p)
  calc
    ‖∫ p, f (u + w, p)‖ ≤ ∫ p, ‖f (u + w, p)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, F (u, p) := by
      apply integral_mono (hf_slice (u + w)).norm (hF_slice u)
      intro p
      change ‖f (u + w, p)‖ ≤ wienerEnvelope f 1 (u, p)
      apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
      apply Metric.mem_closedBall.mpr
      rw [Prod.dist_eq]
      apply max_le
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      · simp
end Auto
