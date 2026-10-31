-- Prove2me | Definitions.Def_ParallelLotteries_Budget
-- name    : ParallelLotteries_Budget
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:15.174495+00:00
-- url     : https://prove2.me/theorems/dfd4f08e-0173-425a-ba15-e02944bf3f40
-- title:
--   The cost $C(y)=\frac1k\sum_i y_i/p_i$ and the budget problem (51)
-- statement:
--   Fix a number of tickets $k\ge1$ and win probabilities $p\in[0,1]^n$. Pricing item $i$ at $1/(kp_i)$, the **cost** of a fractional allocation $y$ is (49)
--   $$C(y)=\frac1k\sum_i \frac{y_i}{p_i}.$$
--   A vector $y$ is **budget-feasible** if it is a fractional allocation, $y\in[0,1]^n$ with $\sum_i y_i\le1$, and $C(y)\le1$. For a type $v$, $y$ **solves the budget problem** (51) if it is budget-feasible and $z\cdot v\le y\cdot v$ for every budget-feasible $z$; the set of such $y$ is the paper's $Y_v=\arg\max_{y:C(y)\le1}y\cdot v$. The **support** of $y$ is the set of its nonzero entries.
--
--   In the proof of Theorem 2, $C$ is a budget: every equilibrium allocation costs at most $1$, and the total cost is preserved by trade reallocations, so the budget problem bounds what a trade can give an agent.
--
--   **Formalization Note** The paper divides by $p_i$ without comment; the sum defining $C$ runs over the items with $p_i>0$, which is (49) verbatim when every $p_i>0$. The feasible set of (51) is read as fractional allocations (otherwise $y\cdot v$ is unbounded).
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (49) and (51), p.32

import Mathlib

namespace ParallelLotteries

/-- **Cost of a fractional allocation**, display (49), Arnosti–Randolph, SSRN 3370605 (preprint),
App. D.2, p.32: `C(y) = (1/k) ∑_i y_i / p_i`, i.e. item `i` is priced at `1/(k p_i)`.

**Formalization Note.** The paper divides by `p_i` without comment, presupposing `p_i > 0`. Here
the sum runs over the items with `p_i > 0` only; when every `p_i > 0` this is (49) verbatim. -/
noncomputable def cost {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  (1 / (k : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), y i / p i

/-- **Feasible set of the budget problem (51)**, Arnosti–Randolph, SSRN 3370605 (preprint),
App. D.2, p.32: fractional allocations `y ∈ [0, 1]ⁿ` with `∑_i y_i ≤ 1` (an agent receives at
most one item) and cost `C(y) ≤ 1`.

**Formalization Note.** (51) writes the constraint `{y : C(y) ≤ 1}` only; `y` ranges over
fractional allocations (the paper calls `y` "a fractional allocation" in (49)), which supplies the
constraints `0 ≤ y_i ≤ 1` and `∑ y_i ≤ 1`. -/
def IsBudgetFeasible {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (y : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i ≤ 1 ∧ cost k p y ≤ 1

/-- **Solutions of the budget problem**, the set `Y_v` of display (51), SSRN 3370605 (preprint),
p.32: `y ∈ argmax_{y : C(y) ≤ 1} y · v`, i.e. `y` is budget-feasible and
`z · v ≤ y · v` for every budget-feasible `z`. -/
def IsBudgetOptimal {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (v : Fin n → ℝ) (y : Fin n → ℝ) : Prop :=
  IsBudgetFeasible k p y ∧ ∀ z, IsBudgetFeasible k p z → ∑ i, z i * v i ≤ ∑ i, y i * v i

/-- The set of nonzero entries of a vector `y : Fin n → ℝ` (the paper's "nonzero entries"). -/
noncomputable def support {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => y i ≠ 0)

end ParallelLotteries


