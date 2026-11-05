-- Prove2me | Definitions.Def_LiquidWelfareFPA_LWstar
-- name    : LiquidWelfareFPA_LWstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:07.775905+00:00
-- url     : https://prove2.me/theorems/5dbfb241-cbad-4d69-8b0c-d86624821087
-- title:
--   Optimal liquid welfare $\mathrm{LW}^*$
-- statement:
--   The **optimal liquid welfare** of the values $v_{it}$ and budgets $B_i$ is the largest liquid welfare of any allocation of the $T$ items:
--
--   $$\mathrm{LW}^*=\max_{O_1,\dots,O_n}\ \sum_{i=1}^n\min\Big\{B_i,\sum_{t\in O_i}v_{it}\Big\},$$
--
--   the maximum over disjoint bundles $O_1,\dots,O_n\subseteq[T]$. With $O_i$ the bundles of a maximizing allocation, $\mathrm{LW}^*_i=\min\{B_i,\sum_{t\in O_i}v_{it}\}$ and $\mathrm{LW}^*=\sum_i\mathrm{LW}^*_i$.
--
--   **Formalization Note** An allocation is a map from rounds to `Option (Fin n)`: an item may stay unallocated. Since values are nonnegative this does not change the maximum. The maximum is a finite maximum over a nonempty finite set.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3, p.6 and Lemma 4.1, p.7

import Mathlib
import Definitions.Def_LiquidWelfareFPA_Outcome

namespace LiquidWelfareFPA

/-- **Optimal liquid welfare `LW*`.**
Fikioris & Tardos, arXiv:2210.07502v4, §3, p.6 ("We denote the optimal liquid welfare
LW* = ∑_i LW*_i") and p.7, Lemma 4.1 ("the allocation that maximizes the total liquid welfare").

`LWstar B o` is the maximum, over all allocations `a` of the `T` items (each item `t` goes to a
player `a t = some i` or stays unallocated, `a t = none`), of
`∑_i min{B_i, ∑_{t : a t = some i} v_it}`, with the values `v` of the outcome `o`.

**Formalization Note** The maximum is a finite `Finset.sup'` over the nonempty finite type
`Fin T → Option (Fin n)`. Items may stay unallocated; since values are nonnegative this does not
change the optimum. -/
def LWstar {n T : ℕ} (B : Fin n → ℝ) (o : Outcome n T) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a : Fin T → Option (Fin n) =>
    ∑ i, min (B i) (∑ t ∈ Finset.univ.filter (fun t => a t = some i), o.v i t)

end LiquidWelfareFPA


