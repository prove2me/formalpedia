-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSB
-- name    : DiscreteConvex_LConvexFunctions_Quasi_SSQSB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:16:48.268988+00:00
-- url     : https://prove2.me/theorems/9da78a44-1dac-4df7-921a-7900a497ff56
-- title:
--   Semistrict quasi submodularity (SSQSB)
-- statement:
--   Axiom **(SSQSB)**: for any $p, q \in \mathbb Z^V$, both (i) $g(p\vee q) \ge g(q) \Rightarrow g(p\wedge q) \le g(p)$ and (ii) $g(p\wedge q) \ge g(p) \Rightarrow g(p\vee q) \le g(q)$ hold.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSB).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSB)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.199, axiom (SSQSB): semistrict quasi
submodularity, in `DiscreteConvex.LConvexFunctions.Quasi`.
-/

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Axiom **(SSQSB)**: for any `p, q ∈ Zⱽ`, both (i) `g(p ∨ q) ≥ g(q) → g(p ∧ q) ≤ g(p)` and
(ii) `g(p ∧ q) ≥ g(p) → g(p ∨ q) ≤ g(q)` hold. -/
def SSQSB {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, (g (p ⊔ q) ≥ g q → g (p ⊓ q) ≤ g p) ∧ (g (p ⊓ q) ≥ g p → g (p ⊔ q) ≤ g q)

end DiscreteConvex.LConvexFunctions.Quasi


