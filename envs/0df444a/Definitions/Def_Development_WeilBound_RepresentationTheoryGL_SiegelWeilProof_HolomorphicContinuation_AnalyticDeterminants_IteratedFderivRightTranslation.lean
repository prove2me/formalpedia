-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:45.518156+00:00
-- url     : https://prove2.me/theorems/18278152-9b9f-49d1-86df-809c87c82031
-- title:
--   Iterated Fderiv Right Translation
-- statement:
--   Definitions and structural lemmas for Iterated Fderiv Right Translation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFderivRightTranslation.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def mulR (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ c).toContinuousLinearMap
def mulL (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ c).toContinuousLinearMap
def rit (F : M2 n → ℂ) : (N : ℕ) → (Fin N → M2 n) → M2 n → ℂ
  | 0, _ => F
  | N + 1, W => fun y => fderiv ℂ (rit F N (fun i => W i.succ)) y (y * W 0)
end PositivityTheory.Rg.Sw.LVs


