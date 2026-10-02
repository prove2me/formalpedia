-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSB
-- name    : DiscreteConvex_LConvexFunctions_Quasi_QSB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:16:47.095056+00:00
-- url     : https://prove2.me/theorems/58d2c526-c95c-4ec1-b49c-65066e5ed9c8
-- title:
--   Quasi submodularity (QSB)
-- statement:
--   Axiom **(QSB)**: for any $p, q \in \mathbb Z^V$, $g(p \wedge q) \le g(p)$ or $g(p \vee q) \le g(q)$. A function $g$ satisfying this is **quasi submodular**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSB).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSB)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.199, axiom (QSB): quasi submodularity, in
`DiscreteConvex.LConvexFunctions.Quasi`.
-/

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Axiom **(QSB)**: for any `p, q ∈ Zⱽ`, `g(p ∧ q) ≤ g(p)` or `g(p ∨ q) ≤ g(q)`. A function
`g` is **quasi submodular** if it satisfies this. -/
def QSB {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g (p ⊓ q) ≤ g p ∨ g (p ⊔ q) ≤ g q

end DiscreteConvex.LConvexFunctions.Quasi


