-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:48:42.019805+00:00
-- url     : https://prove2.me/submissions/c9ff2979-2375-4108-acb7-8ba9a9c42b2e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] [ProperSpace F] [NormedField 𝕜] {f : E → 𝕜} {g : F → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (x : E × F) :
    wienerEnvelope (fun p : E × F ↦ f p.1 * g p.2) 1 x ≤
      wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2 := by
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ closedBall (0 : E) 1 ×ˢ closedBall (0 : F) 1 := by
    have hnorm : ‖z‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp hz
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using (norm_fst_le z).trans hnorm,
      by simpa [Metric.mem_closedBall, dist_eq_norm] using (norm_snd_le z).trans hnorm⟩
  have hfx : ‖f (x.1 + z.1)‖ ≤ wienerEnvelope f 1 x.1 := by
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'.1
  have hgz : ‖g (x.2 + z.2)‖ ≤ wienerEnvelope g 1 x.2 := by
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall hg
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'.2
  change ‖f (x.1 + z.1) * g (x.2 + z.2)‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hfx hgz (norm_nonneg _) (aux_wienerEnvelope_nonneg hf zero_le_one _)
end Auto
