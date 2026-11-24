-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
-- name    : Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:20.092798+00:00
-- url     : https://prove2.me/theorems/8fc2507d-c460-4e0f-a462-7f8e96e026ac
-- title:
--   Mul LPow Apply
-- statement:
--   Definitions and structural lemmas for Mul LPow Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/MulLPowApply.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKOwn
open Filter Topology Complex GlobalTheory.CompanionTheory.OM.SchDiff GlobalTheory.CompanionTheory.OM.GaussSch
open scoped SchwartzMap ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def expo (L : V →L[ℝ] ℝ) (Q : V → ℂ) (q : ℂ × V) : ℂ := q.1 * (L q.2 : ℂ) + Q q.2
def mulL (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ fun x => ((L x : ℝ) : ℂ)
variable (L : V →L[ℝ] ℝ) {Q : V → ℂ} {w : ℝ}
end PositivityTheory.ThKOwn
end


