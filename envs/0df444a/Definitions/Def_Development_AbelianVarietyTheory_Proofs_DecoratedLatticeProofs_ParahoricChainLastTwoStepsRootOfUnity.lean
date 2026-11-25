-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnity
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnity
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:35.02882+00:00
-- url     : https://prove2.me/theorems/03be11f1-4a33-58df-a460-4f6bfa006333
-- title:
--   Parahoric Chain Last Two Steps Root Of Unity
-- statement:
--   Definitions and structural lemmas for Parahoric Chain Last Two Steps Root Of Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ParahoricChainLastTwoStepsRootOfUnity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.LevelLaw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
end GlobalTheory.LevelLaw


