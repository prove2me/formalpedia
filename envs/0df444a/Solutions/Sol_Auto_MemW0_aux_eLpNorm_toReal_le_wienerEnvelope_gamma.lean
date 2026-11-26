-- Prove2me | solution 1 for Auto.MemW0.aux_eLpNorm_toReal_le_wienerEnvelope_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:20.484014+00:00
-- url     : https://prove2.me/submissions/bb8e931f-54c0-49e6-a876-8343e2fb8a3f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_unitClosedBallVolume_eq_gamma
public import Theorems.Thm_Auto_MemW0_eLpNorm_toReal_le_wienerEnvelope

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    {q : ℝ} (hq : 1 ≤ q) (hd : 0 < d) :
    (eLpNorm f (ENNReal.ofReal q) volume).toReal ≤
      ((Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) ^ (q⁻¹ - 1) *
        ∫ x, wienerEnvelope f 1 x := by
  rw [← aux_unitClosedBallVolume_eq_gamma hd]
  exact hf.eLpNorm_toReal_le_wienerEnvelope hq
end MemW0
end Auto
