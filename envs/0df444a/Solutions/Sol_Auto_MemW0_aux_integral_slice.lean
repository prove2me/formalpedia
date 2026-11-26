-- Prove2me | solution 1 for Auto.MemW0.aux_integral_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:06.445305+00:00
-- url     : https://prove2.me/submissions/92d8cbe1-ca62-49a2-ab33-7f79003f6893

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope_prod
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice
public import Theorems.Thm_Auto_aux_continuous_integral_slice

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    MemW0 (fun u ↦ ∫ v, f (u, v)) := by
  let F : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → ℝ :=
    wienerEnvelope f 1
  have hF : MemW0 F := hf.aux_mem_wienerEnvelope_prod zero_le_one
  have hF_slice (u : EuclideanSpace ℝ (Fin m)) : Integrable (fun v ↦ F (u, v)) :=
    (hF.aux_memW0_slice u).aux_integrable
  have hf_slice (u : EuclideanSpace ℝ (Fin m)) : Integrable (fun v ↦ f (u, v)) :=
    (hf.aux_memW0_slice u).aux_integrable
  have hcont : Continuous (fun u ↦ ∫ v, f (u, v)) := aux_continuous_integral_slice hf
  refine ⟨hcont, ?_⟩
  have hH : Integrable (fun u ↦ ∫ v, F (u, v)) := hf.2.integral_prod_left
  refine hH.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun u ↦ aux_wienerEnvelope_nonneg hcont zero_le_one u)
    (ae_of_all _ fun u ↦ ?_)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨w, hw, rfl⟩
  change ‖∫ v, f (u + w, v)‖ ≤ ∫ v, F (u, v)
  calc
    ‖∫ v, f (u + w, v)‖ ≤ ∫ v, ‖f (u + w, v)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, F (u, v) := by
      apply integral_mono (hf_slice (u + w)).norm (hF_slice u)
      intro v
      change ‖f (u + w, v)‖ ≤ wienerEnvelope f 1 (u, v)
      apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
      apply Metric.mem_closedBall.mpr
      rw [Prod.dist_eq]
      apply max_le
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      · simp
end MemW0
end Auto
