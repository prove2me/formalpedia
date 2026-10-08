-- Prove2me | Definitions.Def_ForwardRM_Cutoffs_Cutoff
-- name    : ForwardRM_Cutoffs_Cutoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:32:12.885991+00:00
-- url     : https://prove2.me/theorems/57a50a77-696b-44ea-a1e8-64fc65fe94ea
-- title:
--   (4.4), (4.5), p. 17 — ΔΠ^k_t, the cutoff x^k_t, sell ≥ 1 tomorrow, DΠ^k_t and decreasing demand
-- statement:
--   This file defines the difference functions of §4.1–§4.2 and the cutoff.
--
--   With $k$ units in period $t$, highest buyer $y^1$ and lower buyers $y^{-1}$, the profits from selling no unit and exactly one unit today are
--
--   $$
--   \Pi^k_t(\text{sell 0 today})=\delta\tilde\Pi^k_{t+1}(y^1,y^{-1}),\qquad \Pi^k_t(\text{sell 1 today})=m(y^1)+\delta\tilde\Pi^{k-1}_{t+1}(y^{-1}),
--   $$
--
--   as in (4.4)–(4.5), and the **difference function** is $\Delta\Pi^k_t(y^1,y^{-1})=\Pi^k_t(\text{sell 1 today})-\Pi^k_t(\text{sell 0 today})$. The **cutoff** is defined from the model alone, with no lower buyers present:
--
--   $$
--   x^k_t=\inf\{y\in[\underline v,\bar v]:\ \Delta\Pi^k_t(y,\varnothing)\ge 0\}.
--   $$
--
--   For §4.2, write $\mathbf v_{t+1}$ for the period-$(t+1)$ entrants, $v^1_{t+1}$ for the highest of them, and $\{y^1,\mathbf v_{t+1}\}^2_k$ for the 2nd to $k$-th highest values among $y^1$ and the entrants. With $y^{-1}=\varnothing$,
--
--   $$
--   \Pi^k_t(\text{sell}\ge 1\text{ tomorrow})=\delta E_{t+1}\Big[\max\{m(y^1),m(v^1_{t+1})\}+\Pi^{k-1}_{t+1}(\{y^1,\mathbf v_{t+1}\}^2_k)\Big],
--   $$
--
--   and $D\Pi^k_t(y^1)=\Pi^k_t(\text{sell 1 today})-\Pi^k_t(\text{sell}\ge 1\text{ tomorrow})$. Finally, **demand is weakly decreasing in the usual stochastic order** if $N_{t+1}\le_{st}N_t$ for all consecutive periods $t,t+1\in\{1,\dots,T\}$, i.e. $P(N_{t+1}>x)\le P(N_t>x)$ for every real $x$.
--
--   These are the quantities whose roots and monotonicity Theorems 1 and 2 describe.
--
--   **Formalization Note** The cutoff is not defined as the threshold of an optimal policy; that it governs the optimal choice is the content of Theorem 1. If the defining set were empty its infimum would be $0$ by Lean's convention, and Theorem 1 (which asserts $x^k_t\in[\underline v,\bar v]$ and $\Delta\Pi^k_t(x^k_t)=0$) would be false, so this convention cannot trivialize anything. When nobody enters in period $t+1$, $v^1_{t+1}$ is absent and the maximum is $m(y^1)$ (footnote 15's "entries equal zero" read as "no buyer"). The expectation of the sum is written as the sum of expectations, and $E[\max\{a,X\}]$ as $a+E[(X-a)^+]$. The usual stochastic order is the published platform definition `StochasticOrders.Usual.UsualOrder`, applied to the laws of $N_{t+1}$ and $N_t$ on $\mathbb N$.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 15, eqs. (4.4)–(4.5) and the difference function; p. 17, §4.2, definitions of Π^k_t(sell ≥ 1 tomorrow) and DΠ^k_t, footnote 15

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction

namespace ForwardRM.Cutoffs

open MeasureTheory

/-- `{y¹, v}²_k`: the 2nd to `k`-th highest values of the buyers `U`, as a multiset
(fewer if fewer than `k` buyers are present; footnote 15, p. 17). -/
noncomputable def secondToKth (k : ℕ) (U : Multiset ℝ) : Multiset ℝ :=
  ((((sortDesc U).drop 1).take (k - 1) : List ℝ) : Multiset ℝ)

namespace Model

variable (M : Model)

/-- (4.4), p. 15: `Π^k_t(sell 0 today) = δ Π̃^k_{t+1}(y¹, y^{-1})`, where `S` is the multiset of
lower buyers `y^{-1}`. -/
noncomputable def sellZeroToday (t k : ℕ) (y1 : ℝ) (S : Multiset ℝ) : ℝ :=
  M.δ * M.piTilde (t + 1) k (y1 ::ₘ S)

/-- (4.5), p. 15: `Π^k_t(sell 1 today) = m(y¹) + δ Π̃^{k−1}_{t+1}(y^{-1})`. -/
noncomputable def sellOneToday (t k : ℕ) (y1 : ℝ) (S : Multiset ℝ) : ℝ :=
  M.m y1 + M.δ * M.piTilde (t + 1) (k - 1) S

/-- The difference function `ΔΠ^k_t(y¹, y^{-1}) = Π^k_t(sell 1 today) − Π^k_t(sell 0 today)`
(p. 15). -/
noncomputable def deltaPi (t k : ℕ) (y1 : ℝ) (S : Multiset ℝ) : ℝ :=
  M.sellOneToday t k y1 S - M.sellZeroToday t k y1 S

/-- The cutoff `x^k_t`, defined from the model alone as the least value `y ∈ [v̲, v̄]` of the
highest buyer, with no lower buyers present (`y^{-1} = ∅`), at which selling one unit today is
weakly better than selling none: `x^k_t = inf {y ∈ [v̲, v̄] | ΔΠ^k_t(y, ∅) ≥ 0}`.
(Theorem 1 asserts that this number governs the optimal allocation for every `y^{-1}` and is the
unique root of `ΔΠ^k_t`; if the set were empty, `sInf ∅ = 0`, and Theorem 1 would be false.) -/
noncomputable def cutoff (t k : ℕ) : ℝ :=
  sInf {y | y ∈ Set.Icc M.vlo M.vhi ∧ 0 ≤ M.deltaPi t k y 0}

/-- `Π^k_t(sell ≥ 1 tomorrow)` (p. 17), with the lower buyers set to `y^{-1} = ∅`:
`δ E_{t+1}[max{m(y¹), m(v¹_{t+1})} + Π^{k−1}_{t+1}({y¹, v_{t+1}}²_k)]`.
When nobody enters in period `t+1`, `v¹_{t+1}` is absent and the maximum is `m(y¹)`
(`headD` returns `y¹`). The expectation of the sum is written as the sum of the expectations;
`E[max{a, X}]` is `expMaxWith`. -/
noncomputable def sellTomorrow (t k : ℕ) (y1 : ℝ) : ℝ :=
  M.δ * (M.expMaxWith (t + 1) (M.m y1) (fun C => M.m ((sortDesc C).headD y1)) +
    M.cohortExp (t + 1) (fun C => M.piVal (t + 1) (k - 1) (secondToKth k (y1 ::ₘ C))))

/-- `DΠ^k_t(y¹) = Π^k_t(sell 1 today) − Π^k_t(sell ≥ 1 tomorrow)` (p. 17), with `y^{-1} = ∅`. -/
noncomputable def DPi (t k : ℕ) (y1 : ℝ) : ℝ :=
  M.sellOneToday t k y1 0 - M.sellTomorrow t k y1

/-- Demand is weakly decreasing in the usual stochastic order (§4.2, p. 17):
`N_{t+1} ≤_st N_t` for all consecutive periods `t, t+1 ∈ {1, …, T}`, i.e.
`P(N_{t+1} > x) ≤ P(N_t > x)` for every real `x`. -/
def DecreasingDemand : Prop :=
  ∀ t, 1 ≤ t → t + 1 ≤ M.T →
    StochasticOrders.Usual.UsualOrder (M.arrivals (t + 1)).toMeasure (M.arrivals t).toMeasure
      (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ))

end Model

end ForwardRM.Cutoffs


