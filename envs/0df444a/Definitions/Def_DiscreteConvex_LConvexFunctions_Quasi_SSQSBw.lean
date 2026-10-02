-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSBw
-- name    : DiscreteConvex_LConvexFunctions_Quasi_SSQSBw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:09.71931+00:00
-- url     : https://prove2.me/theorems/d2ecb290-6ece-486a-afe5-5d911957845a
-- title:
--   Weak semistrict quasi submodularity (SSQSBw)
-- statement:
--   Axiom **(SSQSBw)**: for any $p, q \in \operatorname{dom} g$, either (i) $\max(g(p),g(q)) > \min(g(p\wedge q),g(p\vee q))$ or (ii) $g(p)=g(q)=g(p\wedge q)=g(p\vee q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (SSQSBw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (SSQSBw)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.200, axiom (SSQSBw): the weak variant of
semistrict quasi submodularity, in `DiscreteConvex.LConvexFunctions.Quasi`.
-/

open DiscreteConvex.LConvexFunctions

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Axiom **(SSQSBw)**: for any `p, q ∈ dom g`, either (i) `max(g(p), g(q)) >
min(g(p ∧ q), g(p ∨ q))` or (ii) `g(p) = g(q) = g(p ∧ q) = g(p ∨ q)`. -/
def SSQSBw {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g,
    max (g p) (g q) > min (g (p ⊓ q)) (g (p ⊔ q)) ∨
      (g p = g q ∧ g q = g (p ⊓ q) ∧ g (p ⊓ q) = g (p ⊔ q))

end DiscreteConvex.LConvexFunctions.Quasi


