-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:34.549804+00:00
-- url     : https://prove2.me/theorems/fd09b736-bb93-46ae-967a-9a58c846ff1e
-- title:
--   Map Of Real Mul
-- statement:
--   Definitions and structural lemmas for Map Of Real Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean

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
open scoped Real
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace C
end C
open C
namespace C
def lo (t : ℝ) : Mat l := fromBlocks 1 0 (t • 1) 1
end C
end PositivityTheory.ThKR.Mp


