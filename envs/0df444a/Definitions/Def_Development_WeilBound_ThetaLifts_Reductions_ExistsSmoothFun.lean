-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
-- name    : Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:06.294959+00:00
-- url     : https://prove2.me/theorems/78a5d0bc-ab91-40ff-a8cf-af23b47170c4
-- title:
--   Exists Smooth Fun
-- statement:
--   Definitions and structural lemmas for Exists Smooth Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/ExistsSmoothFun.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform
namespace PositivityTheory.ThKR
variable {l : Type} [Fintype l] [DecidableEq l]
end PositivityTheory.ThKR


