-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_QuotIntPosOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_QuotIntPosOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:37.581916+00:00
-- url     : https://prove2.me/theorems/568af73f-f831-404f-b02c-c1d0cb7001bc
-- title:
--   Quot Int Pos One
-- statement:
--   Definitions and structural lemmas for Quot Int Pos One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/QuotIntPosOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsQuotIntCellsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)
noncomputable section
namespace GlobalTheory.PosOneCell
section Lemmas
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]
end Lemmas
end GlobalTheory.PosOneCell


