-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:46.225463+00:00
-- url     : https://prove2.me/theorems/6b100057-29f2-401d-905a-d9f0bd77a8db
-- title:
--   Exists Finset Generating Operator Stable Bounded
-- statement:
--   Definitions and structural lemmas for Exists Finset Generating Operator Stable Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetGeneratingOperatorStableBounded.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.StabGen
open GlobalTheory.TensHead
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}
noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)
end GlobalTheory.StabGen


