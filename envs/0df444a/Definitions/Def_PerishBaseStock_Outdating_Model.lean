-- Prove2me | Definitions.Def_PerishBaseStock_Outdating_Model
-- name    : PerishBaseStock_Outdating_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:42:49.590143+00:00
-- url     : https://prove2.me/theorems/63624e57-97c7-4670-bb6a-aa533de18b5f
-- title:
--   §2, pp. 8–9, (1)–(2) — the FIFO lost-sales perishable inventory system, admissible policies, $C^\pi$, $\mathrm{OPT}_\theta$ and $C_\theta(S)$
-- statement:
--   This file sets up the periodic-review inventory system of a perishable product with a fixed lifetime, lost sales, zero lead time and FIFO issuance, as in §2 of Bu, Gong and Chao.
--
--   **Data.** The product has a lifetime of $m\ge 1$ periods. Demands $D_1,D_2,\dots$ are i.i.d. copies of a non-negative random variable $D$ with $0<\mathbb E[D]<\infty$ (the demand law of the referenced definition `CappedBaseStock_Model`). Unit costs are a holding cost $h>0$ for every unit left over after demand, a lost-sales penalty $p>0$ per unit of unmet demand, and an additional outdating cost $\theta\ge 0$ per unit that perishes.
--
--   **State and dynamics.** At the start of period $t$ the state is $x_t=(x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the stock whose remaining lifetime is at most $i$ periods (a cumulative level). The firm orders $q_t\ge 0$, raising the total stock to $x_{t,m}=x_{t,m-1}+q_t$ (with $x_{t,0}=0$). Demand $D_t$ is served oldest first; the amount outdating at the end of the period is $o_t=(x_{t,1}-D_t)^+$, and
--   $$x_{t+1,i}=(x_{t,i+1}-D_t-o_t)^+,\qquad i=1,\dots,m-1.\tag{1}$$
--   The system starts empty, $x_1=0$.
--
--   **Policies and costs.** A policy $\pi$ is *admissible* if in each period $t$ its order is $\varphi^\pi_t(x_t)$ for a non-negative measurable function $\varphi^\pi_t$; $\Pi$ is the set of admissible policies. The period cost is
--   $$C^\pi_t=h(x^\pi_{t,m}-D_t)^+ + p(D_t-x^\pi_{t,m})^+ + \theta o^\pi_t,\tag{2}$$
--   the long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$, and $\mathrm{OPT}_\theta=\inf_{\pi\in\Pi}C^\pi$. The base-stock policy $\pi_S$, $S\ge 0$, orders $q_t=(S-x_{t,m-1})^+$, and $C_\theta(S)$ is its long-run average cost.
--
--   These objects are the cost side of Theorem 4: the optimality gap $C_\theta(\widetilde S_\theta)-\mathrm{OPT}_\theta$ compares the simulated cost of a base-stock policy with the optimal cost over all admissible policies.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$ and the demand path coordinate `d t` is $D_{t+1}$. The state is `Fin (m - 1) → ℝ≥0` (empty when $m=1$, in which case $x_{t,1}=x_{t,m}$ and everything left over outdates); truncated subtraction on $\mathbb R_{\ge0}$ is the positive part. Costs live in $[0,\infty]$, expectations are lower Lebesgue integrals over the i.i.d. demand-path law, and the Cesàro average uses horizons $T+1$, which has the same limsup as $\frac1T\sum_{t=1}^T$. $\theta$ is not a field of `Params` but an explicit argument in $\mathbb R_{\ge0}$, because Theorem 4 lets it vary. $\Pi$ is exactly the paper's class: deterministic, time-dependent, Markov in the state.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–9, §2, (1), (2), §2.1

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_PerishBaseStock_Population_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Outdating

/-- The cost and lifetime data of the FIFO lost-sales perishable system (p. 8): lifetime
`m ≥ 1`, unit holding cost `h > 0` and unit penalty cost `p > 0`. The unit outdating cost
`θ ≥ 0` is the parameter sent to infinity in this mission, so it is passed separately as
`θ : ℝ≥0`. -/
structure Params where
  m : ℕ
  one_le_m : 1 ≤ m
  h : ℝ
  p : ℝ
  h_pos : 0 < h
  p_pos : 0 < p

/-- The cumulative level `x_{t,i}` for `i = 1, …, m`, with the order-up-to level
`x_{t,m} = y` supplied separately (for `i ≥ m` the value is `y`). -/
def cumLevel {m : ℕ} (x : PerishBaseStock.Population.State m) (y : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if hi : 1 ≤ i ∧ i < m then x ⟨i - 1, by omega⟩ else y

/-- The total stock before ordering, `x_{t,m-1}`, with the convention `x_{t,0} = 0`
when `m = 1`. -/
def onHand {m : ℕ} (x : PerishBaseStock.Population.State m) : ℝ≥0 :=
  if hm : 2 ≤ m then x ⟨m - 2, by omega⟩ else 0

/-- Outdating under FIFO (p. 8): `o_t = (x_{t,1} - D_t)^+`, where `x_{t,1}` is the
order-up-to level `y = x_{t,m}` when `m = 1`. Truncated subtraction on `ℝ≥0` is the
positive part. -/
def outdated {m : ℕ} (x : PerishBaseStock.Population.State m) (y d : ℝ≥0) : ℝ≥0 :=
  cumLevel x y 1 - d

/-- The FIFO dynamics (1), p. 8: `x_{t+1,i} = (x_{t,i+1} - D_t - o_t)^+`,
`i = 1, …, m - 1`, given the order-up-to level `y = x_{t,m}` and demand `d = D_t`. -/
def step {m : ℕ} (x : PerishBaseStock.Population.State m) (y d : ℝ≥0) : PerishBaseStock.Population.State m :=
  fun i => cumLevel x y (i.val + 2) - d - outdated x y d

/-- The total inventory level after ordering, `x^π_{t,m} = x^π_{t,m-1} + q^π_t`. -/
def orderUpTo {m : ℕ} (π : PerishBaseStock.Population.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ≥0 :=
  onHand (PerishBaseStock.Population.run π d t) + π.φ t (PerishBaseStock.Population.run π d t)

/-- The outdated quantity `o^π_t`. -/
def outdatedAt {m : ℕ} (π : PerishBaseStock.Population.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ≥0 :=
  outdated (PerishBaseStock.Population.run π d t) (orderUpTo π d t) (d t)

/-- The period cost (2): `C^π_t = h(x^π_{t,m} - D_t)^+ + p(D_t - x^π_{t,m})^+ + θ o^π_t`,
valued in `ℝ≥0∞`. -/
def periodCost (c : Params) (θ : ℝ≥0) (π : PerishBaseStock.Population.Policy c.m) (d : CappedBaseStock.DemandPath)
    (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal c.h * ((orderUpTo π d t - d t : ℝ≥0) : ℝ≥0∞) +
    ENNReal.ofReal c.p * ((d t - orderUpTo π d t : ℝ≥0) : ℝ≥0∞) +
    (θ : ℝ≥0∞) * (outdatedAt π d t : ℝ≥0∞)

/-- The long-run average cost `C^π = limsup_{T→∞} (1/T) ∑_{t=1}^T E[C^π_t]`, with the
expectation a lower Lebesgue integral over the i.i.d. demand path law. -/
def policyCost (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (π : PerishBaseStock.Population.Policy c.m) :
    ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1),
        ∫⁻ d, periodCost c θ π d t ∂CappedBaseStock.demandPathLaw P) /
      ((T : ℝ≥0∞) + 1)) Filter.atTop

/-- The optimal cost `OPT_θ = inf_{π ∈ Π} C^π`, over all admissible policies. -/
def OPT (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) : ℝ≥0∞ :=
  ⨅ π : PerishBaseStock.Population.Policy c.m, policyCost P c θ π

lemma measurable_onHand (m : ℕ) : Measurable (onHand : PerishBaseStock.Population.State m → ℝ≥0) := by
  unfold onHand
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The base-stock policy `π_S` (p. 9): order `q_t = (S - x_{t,m-1})^+`. -/
def baseStock (m : ℕ) (S : ℝ≥0) : PerishBaseStock.Population.Policy m where
  φ _ x := S - onHand x
  measurable_φ _ := measurable_const.sub (measurable_onHand m)

/-- `C_θ(S)`, the long-run average cost of the base-stock policy `π_S`. -/
def bsCost (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost P c θ (baseStock c.m S)

end PerishBaseStock.Outdating


