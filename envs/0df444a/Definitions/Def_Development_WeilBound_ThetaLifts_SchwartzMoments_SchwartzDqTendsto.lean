-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_SchwartzDqTendsto
-- name    : Development_WeilBound_ThetaLifts_SchwartzMoments_SchwartzDqTendsto
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:32.192482+00:00
-- url     : https://prove2.me/theorems/7baca021-1bd4-4701-8d12-b8a1d314d218
-- title:
--   Schwartz Dq Tendsto
-- statement:
--   Definitions and structural lemmas for Schwartz Dq Tendsto, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/SchwartzDqTendsto.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
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
open Filter Topology GlobalTheory.CompanionTheory.OM.SchDiff
open scoped SchwartzMap LineDeriv ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
end PositivityTheory.ThKOwn
end


