-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToOneSpherical
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToOneSpherical
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:18.484349+00:00
-- url     : https://prove2.me/theorems/e525878a-7080-5707-a393-b85e43227157
-- title:
--   To One Spherical
-- statement:
--   Definitions and structural lemmas for To One Spherical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ToOneSpherical.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
namespace GlobalTheory.PosOneSpherical
end GlobalTheory.PosOneSpherical


