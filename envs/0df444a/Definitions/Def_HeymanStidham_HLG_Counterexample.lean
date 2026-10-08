-- Prove2me | Definitions.Def_HeymanStidham_HLG_Counterexample
-- name    : HeymanStidham_HLG_Counterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:29:31.941723+00:00
-- url     : https://prove2.me/theorems/e10fee64-40c7-44d5-a4e3-fdb8858757bf
-- title:
--   §3, pp. 991–992 — the counterexample's arrivals tₙ = n and interrupted indicator sojourns
-- statement:
--   This file defines the data of the counterexample of Heyman and Stidham (1980), §3.
--
--   Customer $m \ge 1$ arrives at $t_m = m$. Its total sojourn time is one time unit, divided into $m$ visits of duration $1/m$, one in each of the intervals $[m, m+1), [m+1, m+2), \ldots, [2m-1, 2m)$. Following the page's convention, the visit of customer $m$ in $[m, m+1)$ begins at time $m$, and each later visit in $[k, k+1)$, $k > m$, begins when the visit of customer $m+1$ in that interval ends. Unwinding the convention, the visit of customer $m$ in $[k, k+1)$, $m \le k \le 2m-1$, is
--
--   $$
--   \Big[\,k + \sum_{j=m+1}^{k} \frac1j,\;\; k + \sum_{j=m}^{k} \frac1j\,\Big).
--   $$
--
--   The function $f_m$ is the indicator of the union of these $m$ visits: $f_m(t) = 1$ when customer $m$ is in the system at time $t$, and $0$ otherwise. The page uses the support span $s_m = m$.
--
--   The example shows that indicator functions alone do not guarantee $H = \lambda G$: assumption (ii) of the paper cannot be dropped.
--
--   **Formalization Note** Customers are 0-based in Lean: index $n$ is customer $m = n+1$, with arrival epoch $n+1$, and the visits are indexed by $k \in \{n+1, \ldots, 2n+1\}$. The page notes that the placement of the visits within their unit intervals does not affect $H$; the closed form above is the page's own convention.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), pp. 991–992, §3, Counterexample to H = λG when fₙ Is an Indicator Function (and Figure 1)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

namespace HeymanStidham.HLG

/-! The counterexample of §3, pp. 991–992. Lean index `n` is the paper's customer
`m = n + 1`. -/

/-- Arrival epochs `t_m = m` (p. 991): customer `m = n + 1` arrives at time `n + 1`. -/
def cxArrival (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The support span `s_m = m` used in the counterexample (p. 992), with customer
`m = n + 1` in Lean indexing. -/
def cxSpan (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The visit of customer `m` in the time interval `[k, k + 1)`, `m ≤ k ≤ 2m − 1`:
`[k + Σ_{j=m+1}^{k} 1/j, k + Σ_{j=m}^{k} 1/j)`, of length `1/m`. For `k = m` it starts at
`m`; for `k > m` it starts where the visit of customer `m + 1` in `[k, k + 1)` ends (p. 992). -/
noncomputable def cxVisit (m k : ℕ) : Set ℝ :=
  Set.Ico ((k : ℝ) + ∑ j ∈ Finset.Ioc m k, (1 : ℝ) / j)
    ((k : ℝ) + ∑ j ∈ Finset.Icc m k, (1 : ℝ) / j)

/-- `f_m(t)`, the indicator that customer `m = n + 1` is in the system at time `t`: the union
of its `m` visits, one in each of `[m, m + 1), …, [2m − 1, 2m)` (pp. 991–992). -/
noncomputable def cxF (n : ℕ) (τ : ℝ) : ℝ :=
  Set.indicator (⋃ k ∈ Finset.Icc (n + 1) (2 * n + 1), cxVisit (n + 1) k) (fun _ => (1 : ℝ)) τ

end HeymanStidham.HLG


