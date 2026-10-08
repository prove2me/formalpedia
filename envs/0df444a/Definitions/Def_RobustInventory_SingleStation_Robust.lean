-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Robust
-- name    : RobustInventory_SingleStation_Robust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:09:20.140335+00:00
-- url     : https://prove2.me/theorems/450dc08d-d53d-4b7f-ab38-f6d847b551c5
-- title:
--   §3.1, formulation (14) — the robust single-station inventory problem
-- statement:
--   The **robust formulation** (14) of Bertsimas and Thiele has, besides the orders $u_k$, epigraph variables $y_k$ and dual variables $q_k$, $r_{ik}$ ($i \le k$), for $k = 0,\dots,T-1$. A point $(u, y, q, r)$ is **feasible** if for every $k < T$
--   $$u_k \ge 0,\qquad q_k \ge 0,\qquad r_{ik} \ge 0,\quad q_k + r_{ik} \ge \hat w_i\ \ (i \le k),$$
--   $$y_k \ge h\Big(\bar x_{k+1} + q_k\Gamma_k + \sum_{i=0}^{k} r_{ik}\Big),\qquad y_k \ge p\Big(-\bar x_{k+1} + q_k\Gamma_k + \sum_{i=0}^{k} r_{ik}\Big),$$
--   where $\bar x_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - \bar w_i)$. Its objective is
--   $$\sum_{k=0}^{T-1} \big( c\,u_k + K\,\mathbf 1_{\{u_k > 0\}} + y_k \big) = \sum_{k=0}^{T-1} \big(C(u_k) + y_k\big),$$
--   and an **optimal solution** of (14) is a feasible point whose objective is at most that of every feasible point.
--
--   Theorem 3.2 is a statement about the order part $u$ of the optimal solutions of this problem.
--
--   **Formalization Note** The binary variables $v_k$ and the constraint $0 \le u_k \le M v_k$ with "$M$ a large positive number" are replaced by the fixed-cost indicator in the objective, as the paper itself does in (21); for a fixed $u$ and $M \ge \max_k u_k$ the choice $v_k = \mathbf 1_{\{u_k>0\}}$ is optimal, so both give the same optimal value. `r i k` is $r_{ik}$. Optimality is minimality over **all** feasible $(u', y', q', r')$, not a first-order condition.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 154 (PDF 5), §3.1, formulation (14)

import Definitions.Def_RobustInventory_SingleStation_Model

namespace RobustInventory.SingleStation

open Finset

namespace Model

variable (M : Model)

/-- Feasibility in the robust formulation (14) (p. 154), with orders `u`, epigraph variables `y`,
and dual variables `q k = q_k`, `r i k = r_{ik}`: for every period `k < T`,
`u_k ≥ 0`, `q_k ≥ 0`, `r_{ik} ≥ 0` and `q_k + r_{ik} ≥ ŵ_i` for `i ≤ k`, and
`y_k ≥ h (x̄_{k+1} + q_k Γ_k + ∑_{i=0}^{k} r_{ik})`,
`y_k ≥ p (-x̄_{k+1} + q_k Γ_k + ∑_{i=0}^{k} r_{ik})`.
The binary variables `v_k` and the big-`M` constraint `0 ≤ u_k ≤ M v_k` are replaced by the
fixed-cost indicator in the objective (`robustObjective`). -/
def RobustFeasible (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  ∀ k < M.T, 0 ≤ u k ∧ 0 ≤ q k ∧ (∀ i ≤ k, 0 ≤ r i k ∧ M.what i ≤ q k + r i k) ∧
    M.h * (M.xbar u k + q k * M.Γ k + ∑ i ∈ range (k + 1), r i k) ≤ y k ∧
    M.p * (-M.xbar u k + q k * M.Γ k + ∑ i ∈ range (k + 1), r i k) ≤ y k

/-- The objective of (14), `∑_{k=0}^{T-1} (c u_k + K 1{u_k > 0} + y_k) = ∑_{k=0}^{T-1} (C(u_k) + y_k)`. -/
noncomputable def robustObjective (u y : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range M.T, (M.C (u k) + y k)

/-- `(u, y, q, r)` is an optimal solution of the robust formulation (14): it is feasible and its
objective is at most that of every feasible point. -/
def IsRobustOptimal (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  M.RobustFeasible u y q r ∧
    ∀ (u' y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
      M.RobustFeasible u' y' q' r' → M.robustObjective u y ≤ M.robustObjective u' y'

end Model

end RobustInventory.SingleStation


