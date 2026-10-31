-- Prove2me | Definitions.Def_ReviewProvision_secondPeriodPayoff
-- name    : ReviewProvision_secondPeriodPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:27.328221+00:00
-- url     : https://prove2.me/theorems/951a91f8-0aa3-456b-8060-c59a8d9dd2e6
-- title:
--   The firm's optimal second-period revenue and payoff
-- statement:
--   In the second period the firm sets a price $r\ge0$ in each cluster. With customer evaluation $v$, the mass $m$ of customers buys $m(v-hr)$ units, so the revenue is $m(v-hr)r$. The **optimal second-period revenue** in a cluster is
--
--   $$
--   \sup_{r\ge0}\ m(v-hr)r,
--   $$
--
--   and the **optimal second-period payoff** at a vector $\vec v$ of evaluations is the sum of these revenues over the clusters.
--
--   **Formalization Note** The set of revenues is nonempty and bounded above by $mv^2/(4h)$, so the supremum is genuine. Its closed form $m(v^+)^2/(4h)$ is the theorem `eq_3`. The floor at price $0$ matters because $v$ can be negative.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), §3.4, pp.13–14

import Mathlib
import Definitions.Def_ReviewProvision_Params

namespace ReviewProvision

/-- The **second-period revenue** in a cluster at customer evaluation `v` and price `r`:
`m (v − h r) r`. SSRN 3403322 (manuscript of 2021-05-24), §3.4, p.13 (PDF 13). -/
def clusterRevenue (p : Params) (v r : ℝ) : ℝ := p.m * (v - p.h * r) * r

/-- The firm's **optimal second-period revenue** in a cluster: the supremum of `clusterRevenue` over
prices `r ≥ 0`. SSRN 3403322 (manuscript of 2021-05-24), §3.4, pp.13–14 (PDF 13–14).

**Formalization Note.** The set is nonempty (`r = 0`) and bounded above by `m v²/(4h)`, so `sSup` is
the genuine supremum. The closed form `m (v⁺)²/(4h)` is the theorem `eq_3`, not the definition. The
floor at price `0` matters because `v` can be negative (footnote 2, p.10); the printed optimal price
is `p*_{n2} = max{v/2h, 0}`, p.14. -/
noncomputable def optimalRevenue (p : Params) (v : ℝ) : ℝ :=
  sSup (clusterRevenue p v '' Set.Ici 0)

/-- The firm's **optimal second-period payoff** at a realized vector of customer evaluations: the
sum over the clusters of `optimalRevenue`, `Π*_2(~v)`. SSRN 3403322 (manuscript of 2021-05-24), §3.4,
pp.13–14 (PDF 13–14). -/
noncomputable def secondPeriodPayoff {N : ℕ} (p : Params) (v : Fin N → ℝ) : ℝ :=
  ∑ n, optimalRevenue p (v n)

end ReviewProvision


