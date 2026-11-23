-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:23.758902+00:00
-- url     : https://prove2.me/theorems/425bbc3b-5047-41a5-ac97-594a0d6c3bbc
-- title:
--   IILeft
-- statement:
--   Definitions and structural lemmas for IILeft, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IILeft.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def cE (E : M2 n) (s : ℝ) : M2 n := NormedSpace.exp (s • E)
def mulL (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A)
def mulR (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)
end PositivityTheory.Rg.Sw.LVs.II


