-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_maxCircFuel
-- name    : FlowAllocationGames_UnitRanking_maxCircFuel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:20.809423+00:00
-- url     : https://prove2.me/theorems/d559acc1-b310-4b60-95dd-be12f347f731
-- title:
--   Iteration budget of the cancelling loop
-- statement:
--   The iteration budget for a game with $n$ nodes and $m$ edges is
--
--   $$
--   4\,(m + 2n + 1)\,(n + 2)\,\bigl(\operatorname{size}(n + 1) + 2\bigr).
--   $$
--
--   The network $G'$ has $N = n + 1$ nodes, $m' = m + 2n$ edges and costs in $\{-1, +1\}$. By Goldberg and Tarjan, every $m'$ consecutive minimum-mean cancellations multiply the minimum cycle mean by at most $1 - 1/N$; it starts at least $-1$, and with integral costs the circulation is optimal once it exceeds $-1/N$. So at most $m'(N\lceil\ln N\rceil + 1)$ cycles are cancelled, and the budget is at least four times that.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23; Goldberg, Tarjan, J. ACM 36 (1989)

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **The iteration budget of the cancelling loop.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23.

`maxCircFuel n m = 4 · (m + 2n + 1) · (n + 2) · (size (n + 1) + 2)`.

**Formalization Note.** `G′` has `N = n + 1` nodes, `m′ = m + 2n` edges, and costs in `{−1, +1}`.
Goldberg and Tarjan (J. ACM 36 (1989); also Korte–Vygen, *Combinatorial Optimization*, §9.3)
show that every `m′` consecutive minimum-mean cancellations multiply the minimum cycle mean by at
most `1 − 1/N`; it starts at least `−1`, and with integral costs the circulation is optimal once it
exceeds `−1/N`. Hence there are at most `m′ · (N ⌈ln N⌉ + 1)` cancellations, and the budget is at
least four times that bound (`⌈ln N⌉ ≤ size N`). No hypothesis of the mission mentions the
fuel. -/
def maxCircFuel (n m : ℕ) : ℕ := 4 * (m + 2 * n + 1) * (n + 2) * (Nat.size (n + 1) + 2)

end FlowAllocationGames.UnitRanking


