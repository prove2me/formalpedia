-- Prove2me | Definitions.Def_BudgetClock_PostedLB_HardInstance
-- name    : BudgetClock_PostedLB_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:30.692635+00:00
-- url     : https://prove2.me/theorems/c9839109-c400-461a-bc75-5a88283a7fb5
-- title:
--   Theorem 13 proof, p. 25 — the hard family: b_h of value √n, n − 1 bidders of value 1, and the cost profiles of Cases 1–3
-- statement:
--   The instance family of the proof of Theorem 13 (p. 25).
--
--   Among the $n$ sellers, the seller with index $0$ is the **high-value bidder** $b_h$; the other $n-1$ sellers are the **small bidders**. The additive valuation $v_0$ gives $b_h$ the value $\sqrt n$ and each small bidder the value $1$:
--   $$v_0(S)=\sum_{i\in S}w_i,\qquad w_{b_h}=\sqrt n,\quad w_i=1\ (i\neq b_h).$$
--   The file also names the sets $\{b_h\}$ (`highSet`) and $N\setminus\{b_h\}$ (`smallSet`) and the three cost profiles used in the case analysis. In each of them $c_{b_h}=B$:
--
--   1. `allCostB`: every seller has cost $B$ (Case 3);
--   2. `case1Cost`: the small bidder $i$ has cost $p$ and every other seller has cost $B$ (Case 1);
--   3. `case2Cost`: every small bidder has cost $B/(n-1)$ (Case 2).
--
--   These are the objects the three case milestones talk about.
--
--   **Formalization Note** The page prints the Case 2 cost as $1/(n-1)$. Then the $n-1$ small bidders cost $1$ in total, which fits the budget only when $B\ge1$, while the argument needs them to be a budget-feasible solution for every $B$. The cost $B/(n-1)$ is used; it agrees with the page at $B=1$. When $n=0$ the sets and sums are empty; when $n=1$, `smallSet` is empty and the division by $n-1=0$ never matters.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, proof of Theorem 13 (instance family; Cases 1, 2, 3)

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_Setting

namespace BudgetClock.PostedLB

/-- The value of a single seller in the proof of Theorem 13 (p. 25): the seller with index `0` is
the high-value bidder `b_h`, with value `√n`; every other seller has value `1`. -/
noncomputable def hardWeight (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then Real.sqrt n else 1

/-- The additive valuation `v₀` of the proof of Theorem 13 (p. 25):
`v₀(S) = ∑_{i ∈ S} hardWeight n i`, so a single bidder `b_h` (index `0`) has value `√n` and each
of the remaining `n − 1` bidders has value `1`. -/
noncomputable def hardVal (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, hardWeight n i

/-- The set `{b_h}` holding only the high-value bidder (index `0`); empty when `n = 0`. -/
def highSet (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val = 0

/-- The set of the `n − 1` small-value bidders (every index but `0`). -/
def smallSet (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val ≠ 0

/-- The cost profile in which every seller has cost `B` (Case 3, p. 25). Every instance of the
proof's family gives `b_h` the cost `B`; this one gives every small bidder the cost `B` too. -/
def allCostB (n : ℕ) (B : ℝ) : Fin n → ℝ :=
  fun _ => B

/-- The cost profile of Case 1 (p. 25): the small bidder `i` has cost `p` (the first positive price
the mechanism offers to a small bidder) and every other seller, `b_h` included, has cost `B`. -/
noncomputable def case1Cost (n : ℕ) (B : ℝ) (i : Fin n) (p : ℝ) : Fin n → ℝ :=
  Function.update (allCostB n B) i p

/-- The cost profile of Case 2 (p. 25): `b_h` (index `0`) has cost `B` and every small bidder has
cost `B / (n − 1)`. The page prints `1/(n−1)`; with that cost the `n − 1` small bidders together
cost `1`, which fits the budget only if `B ≥ 1`, while the argument needs them to fit the budget
`B` exactly. The cost `B/(n−1)` is the evident intent (it coincides with the page at `B = 1`). -/
noncomputable def case2Cost (n : ℕ) (B : ℝ) : Fin n → ℝ :=
  fun j => if j.val = 0 then B else B / ((n : ℝ) - 1)

end BudgetClock.PostedLB


