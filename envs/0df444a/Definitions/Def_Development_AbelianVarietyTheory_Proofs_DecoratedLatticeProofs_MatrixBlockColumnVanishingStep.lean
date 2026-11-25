-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixBlockColumnVanishingStep
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixBlockColumnVanishingStep
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:29.300798+00:00
-- url     : https://prove2.me/theorems/92f6fdcd-2b57-49d5-9cd5-5cdd28a0bb73
-- title:
--   Matrix Block Column Vanishing Step
-- statement:
--   Definitions and structural lemmas for Matrix Block Column Vanishing Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixBlockColumnVanishingStep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
namespace GlobalTheory.SymChain.ExchangeCol
section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
end SlopeTestRemainingChoices
end GlobalTheory.SymChain.ExchangeCol


