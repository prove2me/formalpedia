-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:31.333174+00:00
-- url     : https://prove2.me/theorems/08b7862a-7a4e-4ae0-9f14-4a9bb31167a1
-- title:
--   Congruence Unipotent Matrix Reduction
-- statement:
--   Definitions and structural lemmas for Congruence Unipotent Matrix Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CongruenceUnipotentMatrixReduction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.TopCongr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
end GlobalTheory.TopCongr


