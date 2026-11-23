-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:48.516257+00:00
-- url     : https://prove2.me/theorems/2d29b5d4-3a71-42c2-a3fb-772523245900
-- title:
--   Cutoff
-- statement:
--   Definitions and structural lemmas for Cutoff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace SmoothCutoff
noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))
noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s
noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1
end SmoothCutoff
end ReciprocityTheory.L2DbarEstimates.I


