-- Prove2me | solution 1 for Auto.MemW0.aux_eLpNorm_one_le_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:17.608027+00:00
-- url     : https://prove2.me/submissions/0a81e531-2e6a-4205-829b-2f1304e2f3ed

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_aux_integral_norm_le_integral_wienerEnvelope
public import Theorems.Thm_Auto_aux_eLpNorm_one_le_of_integral_norm_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    eLpNorm f 1 volume ≤ ENNReal.ofReal (∫ x, wienerEnvelope f 1 x) :=
  aux_eLpNorm_one_le_of_integral_norm_le hf.aux_integrable
    (aux_integral_norm_le_integral_wienerEnvelope hf)
end MemW0
end Auto
