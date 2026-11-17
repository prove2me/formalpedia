-- Prove2me | Definitions.Def_N25_ExplicitF16Distrib
-- name    : N25_ExplicitF16Distrib
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:25.173185+00:00
-- url     : https://prove2.me/theorems/41b3710f-e303-48e7-b4af-6a10ce4b3fda
-- title:
--   Distributivity certificate for the executable $𝔽_{16}$ table
-- statement:
--   This certificate-only file exhaustively checks $$a(b+c)=ab+ac$$ for the quartic polynomial-basis operation table on $𝔽_{16}$. It isolates one of the expensive $16^3$ finite reductions needed to certify that the executable multiplication and addition form a field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
/-!
# Distributivity for the level-25 `F_16` model

This isolated certificate checks all `16^3` triples in the distributive law
for the quartic polynomial-basis operations.  Together with the separate
associativity certificate, it supplies the expensive part of the formal
finite-field interpretation of the point-count table.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Exhaustive ordinary-kernel certificate that multiplication distributes
over addition in the quartic polynomial-basis table. -/
theorem f16_mul_add :
    ∀ a b c : F16,
      f16Operations.mul a (f16Operations.add b c) =
        f16Operations.add (f16Operations.mul a b)
          (f16Operations.mul a c) := by

    exact of_decide_eq_true rfl

end MazurProof.RationalPointsN25QuotientF16Field


