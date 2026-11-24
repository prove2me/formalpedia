-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:30.863472+00:00
-- url     : https://prove2.me/theorems/8c9da35d-6cc0-4658-a577-71a6f70e5a2a
-- title:
--   Le Ker Of Local Finite Length To Simple
-- statement:
--   Definitions and structural lemmas for Le Ker Of Local Finite Length To Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimple.lean

import Mathlib
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
namespace GlobalTheory.TensHead
section HeadKill
variable {W : Type} [AddCommGroup W] [Module ℂ W]
def MinStab (A : Set (Module.End ℂ W)) (T : Submodule ℂ W) : Prop :=
  Stab A T ∧ ∀ U : Submodule ℂ W, Stab A U → U ≤ T → U = ⊥ ∨ U = T
end HeadKill
end GlobalTheory.TensHead


