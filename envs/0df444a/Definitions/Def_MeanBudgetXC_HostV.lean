-- Prove2me | Definitions.Def_MeanBudgetXC_HostV
-- name    : MeanBudgetXC_HostV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:31.947837+00:00
-- url     : https://prove2.me/theorems/4020f135-8600-49b1-95c2-6c012cedc2f4
-- title:
--   Vertex set of the host graph
-- statement:
--   The **vertex set of the host graph** has four blocks:
--
--   1. the private path vertices $(s,i,k)$: a side $s\in\{0,1\}$ (the left or right source group), a source variable $i<n_0$, and a position $k\in\{0,1,2,3\}$ on the path $v_{i,0}-a_i-b_i-v_{i,1}$;
--   2. the vertices $(p,u)$ of the $\ell$ padding copies of $T$, where $T$ has order $t$;
--   3. the two endpoints of each of the $c$ marker edges;
--   4. the $n_{\mathrm{iso}}$ isolated vertices.
--
--   It has $8n_0+t\ell+2c+n_{\mathrm{iso}}$ elements, which is $N$ under (15).
--
--   **Formalization Note** The paper does not name this set; the sum type records the block structure of its construction. Positions $0,1,2,3$ stand for $v_{i,0},a_i,b_i,v_{i,1}$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19

import Mathlib

namespace MeanBudgetXC

/-- The vertex set of the **host graph** of Section 4.3 (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Section 4.3, p.19), in four blocks:
1. the private path vertices `(s, i, k)`: side `s ∈ {0, 1}` (left/right source group), source
   variable `i < n₀`, and position `k ∈ {0, 1, 2, 3}` on the path `v_{i,0} — a_i — b_i — v_{i,1}`
   (`k = 0` is `v_{i,0}`, `1` is `a_i`, `2` is `b_i`, `3` is `v_{i,1}`);
2. the vertices `(p, u)` of the `ℓ` padding copies of `T`, `u` a vertex of the `p`-th copy;
3. the endpoints `(m, b)` of the `c` marker edges;
4. the `n_iso` isolated vertices.
It has `8 n₀ + t ℓ + 2 c + n_iso` vertices, which is `N` under (15). -/
abbrev HostV (n₀ t ℓ c niso : ℕ) : Type :=
  (Fin 2 × Fin n₀ × Fin 4) ⊕ (Fin ℓ × Fin t) ⊕ (Fin c × Fin 2) ⊕ Fin niso

end MeanBudgetXC


