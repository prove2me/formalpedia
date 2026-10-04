-- Prove2me | Definitions.Def_EkelandVP_Constraints_feasibleSet
-- name    : EkelandVP_Constraints_feasibleSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:29:38.375933+00:00
-- url     : https://prove2.me/theorems/df6b1ada-dfac-4ee5-857b-895bfdeca6d7
-- title:
--   The feasible set (3.2): $\mathcal C=\{v : G_i(v)=0,\ 1\le i\le p;\ G_i(v)\ge 0,\ p+1\le i\le m\}$
-- statement:
--   Let $V$ be a set and let $G_1,\dots,G_m : V\to\mathbb R$ be real-valued functions. Single out the first $p$ of them as equality constraints and the remaining ones as inequality constraints. The **feasible set** of the constrained problem (3.1) is
--   $$\mathcal C=\{v\in V \mid G_i(v)=0 \text{ for } 1\le i\le p,\quad G_i(v)\ge 0 \text{ for } p+1\le i\le m\}.$$
--
--   Every statement of this mission (the $\varepsilon$-optimality of $v_\varepsilon$, the tangent curve, Lemma 3.2 and Theorem 3.1) quantifies over this set.
--
--   **Formalization Note.** The constraints form one family `G : Fin m → V → ℝ`, indexed from $0$. The paper's constraint $i$ ($1$-based) is the Lean index $i-1$, so a constraint is an equality constraint iff its Lean index is $<p$ and an inequality constraint iff its Lean index is $\ge p$. The definition makes sense for every $p$; the theorems that need $p\le m$ assume it.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 329, §3, (3.1)–(3.2)

import Mathlib

namespace EkelandVP.Constraints

/-- Ekeland (1974), §3, (3.2): the feasible set
`𝒞 = {v | G_i(v) = 0 for 1 ≤ i ≤ p, G_i(v) ≥ 0 for p+1 ≤ i ≤ m}`.
Constraints are indexed by `Fin m` (0-based): the
page's constraint number `k + 1` (1-based) is the Lean index `k`,
so a Lean index `i` is an equality constraint iff `i.val < p` and an inequality constraint iff `p ≤ i.val`. -/
def feasibleSet {V : Type*} {m : ℕ} (p : ℕ) (G : Fin m → V → ℝ) : Set V :=
  {v | ∀ i : Fin m, (i.val < p → G i v = 0) ∧ (p ≤ i.val → 0 ≤ G i v)}

end EkelandVP.Constraints


