-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- name    : ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:03.095035+00:00
-- url     : https://prove2.me/theorems/d2fd4585-320b-4df8-b418-680d5d533d5e
-- title:
--   Tsupport Db Subset
-- statement:
--   Definitions and structural lemmas for Tsupport Db Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
theorem Smooth.re {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    SmoothR n z (fun x => (f x).re) := by
  intro e he
  have h1 := (Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp
end
end ReciprocityTheory.L2DbarEstimates


