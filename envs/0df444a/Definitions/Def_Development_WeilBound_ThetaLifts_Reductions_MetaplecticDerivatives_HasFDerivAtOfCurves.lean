-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOfCurves
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOfCurves
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:20.801876+00:00
-- url     : https://prove2.me/theorems/d4c12cee-90c5-4f91-8079-5c1e3e7fc313
-- title:
--   Has FDeriv At Of Curves
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Of Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
namespace PositivityTheory.ThKR.Mp.MpG
variable {l : Type} [Fintype l] [DecidableEq l]
end PositivityTheory.ThKR.Mp.MpG
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
end PositivityTheory.ThKR.Mp
end


