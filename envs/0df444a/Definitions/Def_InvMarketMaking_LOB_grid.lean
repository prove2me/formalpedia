-- Prove2me | Definitions.Def_InvMarketMaking_LOB_grid
-- name    : InvMarketMaking_LOB_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:44.555026+00:00
-- url     : https://prove2.me/theorems/9f06933f-a55e-4837-b526-0b05a9231f4e
-- title:
--   Uniform grid $\mathcal G_N=\{n/N : n=0,\dots,N\}$
-- statement:
--   For $N\in\mathbb N_{>0}$ the **uniform $1/N$-grid** on $[0,1]$ is
--   $$
--   \mathcal G_N=\{n/N : n=0,1,\dots,N\}.
--   $$
--   It discretizes prices in Proposition 4.3, and the market maker of Theorem 6.18 uses $\mathcal B^\circ=\mathcal A^\circ=\mathcal G_N$ as its bid and ask grids (Eq. (22)).
--
--   **Formalization Note** At $N=0$ the expression is $\{0\}$ (Lean's $0/0=0$); every statement using the grid assumes $N\ge1$.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 4.3, p. 19, and Eq. (22), p. 46

import Mathlib

namespace InvMarketMaking.LOB

/-- The uniform `1/N`-grid `𝒢_N = {n/N : n = 0, …, N}` on `[0,1]` (Maran, Restelli, Stradi,
arXiv:2610.24562v1, Proposition 4.3, p. 19; the discretized sets `B° = A°` of Eq. (22), p. 46).

**Formalization Note** At `N = 0` Lean's `0/0 = 0` makes this `{0}`; every statement using the
grid assumes `N ≥ 1`, as the paper does (`N ∈ ℕ_{>0}`). -/
noncomputable def grid (N : ℕ) : Finset ℝ :=
  (Finset.range (N + 1)).image (fun n : ℕ => (n : ℝ) / N)

end InvMarketMaking.LOB


