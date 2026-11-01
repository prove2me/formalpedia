-- Prove2me | Definitions.Def_ProactiveUpgrade_Policy
-- name    : ProactiveUpgrade_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:51.042073+00:00
-- url     : https://prove2.me/theorems/1dff7481-f5ed-4c45-ba44-b2c079ef1e38
-- title:
--   Proactive upgrade policies and their expected revenue
-- statement:
--   A **proactive upgrade policy** $\pi$ decides, in each period $t$, for each inventory $x$ and each requested product $i$, whether to offer the customer a free upgrade to product $i+1$. The decision matters only where the optimality equation (12) offers a choice, that is, for $i<m$ and $x_{i+1}>0$; elsewhere the outcome is forced (sell product $i$ if it is in stock).
--
--   The expected revenue $V^\pi_t(x)$ of $\pi$ from period $t$ to the end of the season satisfies the recursion (10) with each maximum in (12) replaced by the branch $\pi$ selects, and $V^\pi_{T+1}=0$.
--
--   **Formalization Note** Policies are Markov in (period, inventory, request), as the paper's decisions "hinge upon ... the inventory position $x(t)$" (p.8). Revenue is computed backward with periods to go, as for $\hat v$.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §3, pp.8–9; §3.2.3, pp.12–13

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model

namespace ProactiveUpgrade

/-- **Proactive upgrade policies** (Chen et al., SSRN 3777846, §3, pp.8–9 and §3.2.3, pp.12–13):
`π t x i` holds when, in period `t` with inventory `x`, the seller offers a free upgrade to a
customer who requests product `i`.

**Formalization Note** Policies are Markov in `(t, x(t), request)`, as the paper's decisions
"hinge upon ... the inventory position x(t)" (p.8). A decision matters only where (12) gives a
choice (`i < m`, `x_{i+1} > 0`); elsewhere the outcome is forced. -/
def Policy (m : ℕ) : Type :=
  ℕ → (Fin m → ℕ) → Fin m → Prop

open Classical in
/-- One period under the decision rule `d` of the period, with continuation value `f`: equation
(10) with every maximum of (12) replaced by the branch `d` selects. -/
noncomputable def policyStep {m : ℕ} (M : Model m) (d : (Fin m → ℕ) → Fin m → Prop)
    (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) : ℝ :=
  ∑ i, M.lam * M.β i *
      (if h : i.val + 1 < m then
        (if d x i ∧ 0 < x (succIdx i h) then offerVal M f x i h else noOfferVal M f x i)
      else noOfferVal M f x i) +
    (M.lam * M.β0 + (1 - M.lam)) * f x

/-- Expected revenue of `π` with `n` periods to go in a season of `T` periods (the current period is
`T + 1 − n`). -/
noncomputable def policyToGo {m : ℕ} (M : Model m) (T : ℕ) (π : Policy m) :
    ℕ → (Fin m → ℕ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => policyStep M (π (T - n)) (policyToGo M T π n)

/-- The expected revenue collected by policy `π` from period `t` to the end of the season
(`1 ≤ t ≤ T + 1`), starting from inventory `x`. -/
noncomputable def policyValue {m : ℕ} (M : Model m) (T : ℕ) (π : Policy m) (t : ℕ)
    (x : Fin m → ℕ) : ℝ :=
  policyToGo M T π (T + 1 - t) x

end ProactiveUpgrade


