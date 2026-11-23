-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
-- name    : ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:05.12619+00:00
-- url     : https://prove2.me/theorems/7f265dce-6b64-46f1-982e-061639712ce4
-- title:
--   As Gab Lim
-- statement:
--   Definitions and structural lemmas for As Gab Lim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
open scoped commutatorElement
variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}
def ResCompat (hle : L ≤ L') (τ' : L' ≃ₐ[F] L') (τ : L ≃ₐ[F] L) : Prop :=
  ∀ x : L, τ' (IntermediateField.inclusion hle x) = IntermediateField.inclusion hle (τ x)
end ReciprocityTheory.DiscreteGroups.GlobalClassField


