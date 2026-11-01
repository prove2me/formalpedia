-- Prove2me | Definitions.Def_CloudCostOpt_history
-- name    : CloudCostOpt_history
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:04:45.258505+00:00
-- url     : https://prove2.me/theorems/f71eece4-73dc-4d7a-bb8d-71253a11303b
-- title:
--   State trajectory $x_1,\dots,x_{t}$ under a policy
-- statement:
--   Fix a policy $\pi$ and a sample point $\omega=(N,U)$. The **state trajectory** is defined recursively:
--
--   1. $x_1=0$: no order has been observed before period $1$;
--   2. in period $t$ the policy observes $x_1,\dots,x_t$ and chooses $a_{i,j,t}(s,l)$; then, for $l'\le L_i-1$,
--
--   $$
--   x_{i,t+1}(0,0)=N(i,t),\qquad x_{i,t+1}(s+1,l')=y_{i,t}(s,l'-1)\,\mathbb 1[l'\ge1]+\tilde y_{i,t}(s,l'),
--   $$
--
--   and $x_{i,t+1}(0,l')=0$ for $l'\ge1$. An order that completes its $L_i$-th step leaves the system.
--
--   This is the recursion (5): an order arriving in period $t$ is first observed at the beginning of period $t+1$ in order-state $(0,0)$.
--
--   **Formalization Note** The function returns the whole history $(x_1,\dots,x_{n+1})$ as a map on `Fin (n+1)`, because the decision of each period depends on it.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, pp.3–4 (timing); §3, p.14, (5)

import Mathlib
import Definitions.Def_CloudCostOpt_Policy
import Definitions.Def_CloudCostOpt_cellFail

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The state trajectory under a policy** on the sample point `ω = (N, U)`: `history S π ω n`
lists `x_1, …, x_{n+1}` (`k ↦ x_{k+1}`).

* `x_1 = 0` (no order has been observed before period 1);
* in period `t = n + 1` the policy decides `a_t = π.a n (x_1, …, x_t)`; then, for `l' ≤ Lᵢ − 1`,
  `x_{t+1}(0, 0) = N (i, t)` (the arrivals of period `t`), and for `s' = s + 1`
  `x_{t+1}(s + 1, l') = y_{i,t}(s, l' − 1) [l' ≥ 1] + ỹ_{i,t}(s, l')`, which is (5);
  orders completing their last step leave (cells `l' ≥ Lᵢ` are `0`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, pp.3–4 (timing: period `t` is `(t − 1, t]`, `x_{i,t}(0,0)` counts the arrivals of period
`t − 1`); §3, p.14, (5). -/
noncomputable def history (S : System) (π : Policy S) (ω : Omega S) :
    (n : ℕ) → Fin (n + 1) → State S
  | 0 => fun _ => fun _ _ _ => 0
  | n + 1 =>
    Fin.snoc (α := fun _ => State S) (history S π ω n) (fun i s' l' =>
      if S.L i ≤ l' then 0 else
      match s' with
      | 0 => if l' = 0 then ω.1 (i, n + 1) else 0
      | s + 1 =>
        (if l' = 0 then 0 else
          cellSucc S ω.2 (n + 1) i s (l' - 1) (π.a n (history S π ω n) i s (l' - 1)))
        + cellFail S ω.2 (n + 1) i s l' (π.a n (history S π ω n) i s l'))

end CloudCostOpt


