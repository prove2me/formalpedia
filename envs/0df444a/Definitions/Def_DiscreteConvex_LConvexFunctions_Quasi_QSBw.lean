-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSBw
-- name    : DiscreteConvex_LConvexFunctions_Quasi_QSBw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:16:59.043986+00:00
-- url     : https://prove2.me/theorems/60e54da8-8513-45a5-86de-b4eabc0ab0b2
-- title:
--   Weak quasi submodularity (QSBw)
-- statement:
--   Axiom **(QSBw)**: for any $p, q \in \operatorname{dom} g$, $\max(g(p),g(q)) \ge \min(g(p\wedge q), g(p\vee q))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (QSBw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (QSBw)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.200, axiom (QSBw): the weak variant of quasi
submodularity, in `DiscreteConvex.LConvexFunctions.Quasi`.
-/

open DiscreteConvex.LConvexFunctions

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Axiom **(QSBw)**: for any `p, q ∈ dom g`, `max(g(p), g(q)) ≥ min(g(p ∧ q), g(p ∨ q))`. -/
def QSBw {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g, max (g p) (g q) ≥ min (g (p ⊓ q)) (g (p ⊔ q))

end DiscreteConvex.LConvexFunctions.Quasi


