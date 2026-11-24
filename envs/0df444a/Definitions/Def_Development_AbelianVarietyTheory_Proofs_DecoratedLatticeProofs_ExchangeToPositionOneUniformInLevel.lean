-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneUniformInLevel
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneUniformInLevel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:54.151238+00:00
-- url     : https://prove2.me/theorems/7daf65e8-de7a-43e8-8905-235d35940335
-- title:
--   Exchange To Position One Uniform In Level
-- statement:
--   Definitions and structural lemmas for Exchange To Position One Uniform In Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneUniformInLevel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
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
namespace GlobalTheory.PosOne.Unif
def conjSub {G : Type} [Group G] (U : Subgroup G) (g : G) : Subgroup G :=
  U.comap (MulAut.conj g⁻¹).toMonoidHom
end GlobalTheory.PosOne.Unif
namespace GlobalTheory.PosOne.Unif
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
end GlobalTheory.PosOne.Unif


