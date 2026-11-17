-- Prove2me | Definitions.Def_N25_ExplicitF16Mul
-- name    : N25_ExplicitF16Mul
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:43.817209+00:00
-- url     : https://prove2.me/theorems/67b8a36d-3c5a-468f-a5ef-c0cd6660ca9b
-- title:
--   Multiplicative associativity modulo $β^4+β+1$
-- statement:
--   This certificate-only file exhaustively verifies associativity of the quartic multiplication table obtained from the relation $β^4=β+1$: $$ (ab)c=a(bc). $$ The isolated $16^3$ check supplies the other expensive triple law in the certified $𝔽_{16}$ model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
/-!
# Multiplicative associativity for the level-25 `F_16` model

This isolated certificate checks all `16^3` multiplication triples in the
quartic polynomial-basis table.  It is separated from the other field laws
because this is one of the two expensive reductions in the `F_16` semantic
bridge.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Exhaustive ordinary-kernel certificate for associativity of multiplication
modulo `beta^4 + beta + 1`. -/
theorem f16_mul_assoc :
    ∀ a b c : F16,
      f16Operations.mul (f16Operations.mul a b) c =
        f16Operations.mul a (f16Operations.mul b c) := by

    exact of_decide_eq_true rfl

end MazurProof.RationalPointsN25QuotientF16Field


