-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_Nat_F000
-- name    : BrownianMotion_Auxiliary_Nat_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:06:28.152699+00:00
-- url     : https://prove2.me/theorems/df98674d-a581-43e0-80b7-0ee7e9ccad94
-- title:
--   Source declarations: BrownianMotion.Auxiliary.Nat
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.Nat, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs


@[expose] public section

lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a


