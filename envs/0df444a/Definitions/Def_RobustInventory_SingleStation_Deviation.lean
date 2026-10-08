-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Deviation
-- name    : RobustInventory_SingleStation_Deviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:09:22.758288+00:00
-- url     : https://prove2.me/theorems/d43bcf62-1d61-4cc6-87a0-558e0562ba54
-- title:
--   §3.1, LP (13) and Eq. (20) — the worst-case deviation $A_k$ and the modified demand $w'_k$
-- statement:
--   For a period $k$, the **auxiliary linear program** (13) of Bertsimas and Thiele is
--   $$\max\ \sum_{i=0}^{k} \hat w_i z_i \quad\text{subject to}\quad \sum_{i=0}^{k} z_i \le \Gamma_k,\quad 0 \le z_i \le 1\ (i = 0,\dots,k),$$
--   and its dual, as it appears in the robust formulation (14), is
--   $$\min\ q\,\Gamma_k + \sum_{i=0}^{k} r_i \quad\text{subject to}\quad q \ge 0,\ r_i \ge 0,\ q + r_i \ge \hat w_i\ (i = 0,\dots,k).$$
--   $A_k$ denotes the optimal value of (13): the worst-case deviation of the cumulative demand up to period $k$ from its nominal value under the budget $\Gamma_k$. By convention $A_{-1} = 0$.
--
--   The **modified demand** (20) is
--   $$w'_k = \bar w_k + \frac{p-h}{p+h}\,\big(A_k - A_{k-1}\big).$$
--
--   These are the two quantities in terms of which Theorem 3.2 describes the optimal robust policy.
--
--   **Formalization Note** $A_k$ is defined as the supremum of the objective values of (13) over its feasible set. That set is nonempty ($z = 0$ is feasible because $\Gamma_k \ge 0$) and bounded above by $\sum_{i\le k}\hat w_i$, so the supremum is the optimal value, not a junk value. The paper writes $A_k = q^*_k\Gamma_k + \sum_i r^*_{ik}$ with $(q^*, r^*)$ "the optimal $q$ and $r$ variables in (14)"; these are not unique in general, and the mission uses, as Remark 1 after Theorem 3.2 does, Problem (13) to define $A_k$. `Aprev k` is $A_{k-1}$ with `Aprev 0 = 0`. The denominator $p + h$ is positive since $p > c > 0$ and $h \ge 0$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 153–155 (PDF 4–6), §3.1, LP (13), formulation (14), Eq. (20); p. 156 (PDF 7), Remark 1 after Theorem 3.2

import Definitions.Def_RobustInventory_SingleStation_Model

namespace RobustInventory.SingleStation

open Finset

namespace Model

variable (M : Model)

/-- `z` is feasible for the auxiliary linear program (13) of period `k`:
`0 ≤ z_i ≤ 1` for `i = 0, …, k` and `∑_{i=0}^{k} z_i ≤ Γ_k`. -/
def LP13Feasible (k : ℕ) (z : ℕ → ℝ) : Prop :=
  (∀ i ≤ k, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i ∈ range (k + 1), z i ≤ M.Γ k

/-- `(q, r)` is feasible for the dual of (13), as it appears in (14):
`q ≥ 0`, and `r_i ≥ 0`, `q + r_i ≥ ŵ_i` for `i = 0, …, k`. -/
def LP13DualFeasible (k : ℕ) (q : ℝ) (r : ℕ → ℝ) : Prop :=
  0 ≤ q ∧ ∀ i ≤ k, 0 ≤ r i ∧ M.what i ≤ q + r i

/-- `A k` is the optimal value `A_k` of the auxiliary linear program (13),
`max {∑_{i=0}^{k} ŵ_i z_i : ∑_{i=0}^{k} z_i ≤ Γ_k, 0 ≤ z_i ≤ 1}`, the worst-case deviation of
the cumulative demand up to period `k` from its nominal value.
The set of values is nonempty (`z = 0` is feasible since `Γ_k ≥ 0`) and bounded above by
`∑_{i=0}^{k} ŵ_i`, so the supremum is the genuine optimal value. -/
noncomputable def A (k : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ z : ℕ → ℝ, M.LP13Feasible k z ∧ v = ∑ i ∈ range (k + 1), M.what i * z i}

/-- `Aprev k = A_{k-1}`, with the paper's convention `A_{-1} = 0` (`q_{-1} = r_{·,-1} = 0`). -/
noncomputable def Aprev : ℕ → ℝ
  | 0 => 0
  | k + 1 => M.A k

/-- The modified demand (20): `w'_k = w̄_k + ((p - h)/(p + h)) (A_k - A_{k-1})`.
The denominator is positive since `p > c > 0` and `h ≥ 0`. -/
noncomputable def wmod (k : ℕ) : ℝ :=
  M.wbar k + (M.p - M.h) / (M.p + M.h) * (M.A k - M.Aprev k)

end Model

end RobustInventory.SingleStation


