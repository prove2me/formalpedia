-- Prove2me | Definitions.Def_CloudCostOpt_Policy
-- name    : CloudCostOpt_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:05.346877+00:00
-- url     : https://prove2.me/theorems/dd82bf79-f9f3-43e0-9c47-9c556b21ffbb
-- title:
--   Policy: a reservation $\mathbf M$ and history-dependent on-demand capacities and assignments satisfying (1)–(2)
-- statement:
--   A **policy** $\pi$ consists of
--
--   1. reserved capacities $M_j\ge0$, $j=1,\dots,J$, chosen once at the beginning of period $1$;
--   2. for every period $t\ge1$ and every history $(x_1,\dots,x_t)$ of observed states, on-demand capacities $m_{j,t}\ge0$, $j=1,\dots,J$, and assignments $a_{i,j,t}(s,l)\in\mathbb N$ of the type-$i$ orders in order-state $(s,l)$ to resource type $j\in\{0,\dots,J\}$,
--
--   such that, for every history,
--
--   $$
--   \sum_{j=0}^{J}a_{i,j,t}(s,l)=x_{i,t}(s,l)\quad\text{for all }(i,s,l)\text{ with }l\le L_i-1,\qquad(2)
--   $$
--
--   $$
--   \sum_{i=1}^{I}\sum_{l=0}^{L_i-1}\sum_{s\le t-2}a_{i,j,t}(s,l)\le M_j+m_{j,t}\quad\text{for all }j\ge1.\qquad(1)
--   $$
--
--   There is no capacity constraint on the dummy resource ($M_0=\infty$).
--
--   **Formalization Note** Non-anticipation is built into the type: the decision of period $t$ is a function of $x_1,\dots,x_t$ only, never of the current period's arrivals or step outcomes. Past decisions are functions of past states, so this is the paper's "every possible history". Capacities are nonnegative reals (the paper's own policy $\pi^*$ reserves $\mu_j+z_j\sqrt{\mu_j}$). Constraints (1)–(2) are imposed on every history, also unreachable ones; on those a decision can always be replaced by "idle everything, rent nothing", so this restricts nothing. The sum in (1) runs over all $s\le t-2$; the cells with $s<l$ are empty along every trajectory.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.4 (Actions, (1), (2), Policy)

import Mathlib
import Definitions.Def_CloudCostOpt_State

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **A policy** (p.4): a one-time reservation `M`, and, in every period, as a function of the
whole observed history, the on-demand capacities `m_t` and the assignment `a_{i,j,t}(s, l)` of the
orders of every cell to resource types, subject to (1) and (2).

Period `t = n + 1` is decided by `m n h` and `a n h`, where the history `h : Fin (n + 1) → State S`
lists the observed states `h k = x_{k+1}`, `k ≤ n`; the current state is `h (Fin.last n) = x_t`.

* `assign_sum` is (2): `Σ_{j=0}^J a_{i,j,t}(s, l) = x_{i,t}(s, l)` for every cell with `l ≤ Lᵢ − 1`;
* `capacity` is (1): `Σ_i Σ_{l=0}^{Lᵢ−1} Σ_{s ≤ t−2} a_{i,j,t}(s, l) ≤ M_j + m_{j,t}` for every real
  resource `j ≥ 1` (here `j : Fin J` stands for type `j.succ`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.4, "Actions", (1)–(2), "Policy".

Formalization Notes:
* Non-anticipation is in the type: the decision of period `t` sees only `x_1, …, x_t`, never the
  current period's arrivals or step outcomes.  Past decisions are functions of past states, so
  observing states only is the paper's "every possible history".
* Capacities `M`, `m` are nonnegative reals (reading): the paper's own policy reserves
  `μ_j + z_j √μ_j`.  Real capacities only enlarge the policy class.
* (1) and (2) are required on every history, also unreachable ones; on those any decision can be
  replaced by "idle everything, rent nothing", so this restricts nothing.
* The sum over `s` in (1) runs over `s < n = t − 1`, i.e. `s ≤ t − 2`, as on the page. -/
structure Policy (S : System) where
  /-- reserved capacities `M_j`, chosen once at the start of period 1 -/
  M : Fin S.J → ℝ≥0
  /-- on-demand capacities `m_{j,t}` in period `t = n + 1` -/
  m : (n : ℕ) → (Fin (n + 1) → State S) → Fin S.J → ℝ≥0
  /-- assignments `a_{i,j,t}(s, l)` in period `t = n + 1` -/
  a : (n : ℕ) → (Fin (n + 1) → State S) → Fin S.I → ℕ → ℕ → Fin (S.J + 1) → ℕ
  /-- constraint (2) -/
  assign_sum : ∀ n h i s l, l < S.L i → ∑ j, a n h i s l j = h (Fin.last n) i s l
  /-- constraint (1) -/
  capacity : ∀ n h (j : Fin S.J),
    ((∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n, a n h i s l j.succ : ℕ) : ℝ≥0) ≤
      M j + m n h j

end CloudCostOpt


