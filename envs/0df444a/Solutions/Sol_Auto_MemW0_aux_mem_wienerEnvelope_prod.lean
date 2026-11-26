-- Prove2me | solution 1 for Auto.MemW0.aux_mem_wienerEnvelope_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:15.745384+00:00
-- url     : https://prove2.me/submissions/e89e8f7a-4486-4a37-9b01-82fa4b1a9b60

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_wienerEnvelope_le
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_prod_of_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) {r : ℝ} (hr : 0 ≤ r) :
    MemW0 (wienerEnvelope f r) := by
  have hcont : Continuous (wienerEnvelope f r) := continuous_wienerEnvelope hf.1 r
  refine ⟨hcont, ?_⟩
  have hinter : Integrable (wienerEnvelope f (r + 1)) :=
    aux_integrable_wienerEnvelope_prod_of_integrable hf.1 zero_lt_one (by linarith) hf.2
  refine hinter.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_wienerEnvelope_le hf.1 hr zero_le_one x
end MemW0
end Auto
