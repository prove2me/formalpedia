-- Prove2me | Definitions.Def_SizeRamsey_Equality_Extension
-- name    : SizeRamsey_Equality_Extension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:21:58.821651+00:00
-- url     : https://prove2.me/theorems/82b14046-6df6-4bbd-84c3-bf2773d2cff2
-- title:
--   Extension
-- statement:
--   Definitions and structural lemmas for Extension, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Extension.lean

module
public import Definitions.Def_SizeRamsey_AInterface
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
def SqHit (a b : Fin 6) : Prop :=
  ∀ p q r s : Fin 6, k33MinusEdge.Adj p q → k33MinusEdge.Adj q r →
    k33MinusEdge.Adj r s → k33MinusEdge.Adj s p → p ≠ r → q ≠ s →
    p = a ∨ p = b ∨ q = a ∨ q = b ∨ r = a ∨ r = b ∨ s = a ∨ s = b
def PathEnds (a b c d c' d' : Fin 6) : Prop :=
  ∀ u x w : Fin 6, u ≠ w → k33MinusEdge.Adj u x → k33MinusEdge.Adj x w →
    (u = a ∨ u = b ∨ x = a ∨ x = b ∨ w = a ∨ w = b) ∨
      (u = c ∧ w = d) ∨ (u = d ∧ w = c) ∨ (u = c' ∧ w = d') ∨ (u = d' ∧ w = c')
end SizeRamsey.Plan


