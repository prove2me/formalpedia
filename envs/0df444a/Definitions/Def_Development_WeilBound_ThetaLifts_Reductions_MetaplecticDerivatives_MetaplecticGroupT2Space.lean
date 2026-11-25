-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:17.343586+00:00
-- url     : https://prove2.me/theorems/13b49124-0928-5409-a91d-6f5bb8d0ee8b
-- title:
--   Metaplectic Group T2 Space
-- statement:
--   Definitions and structural lemmas for Metaplectic Group T2 Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
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
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace MpE
end MpE
open MpE
namespace MpE
end MpE
end PositivityTheory.ThKR.Mp


