-- Prove2me | Definitions.Def_PerishBaseStock_Population_Model
-- name    : PerishBaseStock_Population_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:02.196709+00:00
-- url     : https://prove2.me/theorems/e8bb0804-20a9-4beb-a586-9ca2c9a2ca54
-- title:
--   The FIFO perishable inventory system with zero lead time, its policies, costs, base-stock policy and heuristic level $\widetilde S$ (§2, pp. 8–10)
-- statement:
--   This file sets up the periodic-review inventory system of a perishable product with fixed lifetime $m$, zero lead time, lost sales and FIFO issuance (Bu, Gong & Chao, §2).
--
--   1. **Parameters.** The lifetime $m\ge 1$ (a positive integer), the unit holding cost $h>0$, the unit lost-sales penalty $p>0$ and the unit outdating cost $\theta\ge 0$.
--   2. **Demand.** The demands $D_1,D_2,\dots$ are i.i.d. copies of a non-negative random variable $D$ with $0<\mathbb E[D]<\infty$ and distribution function $F$. The law of $D$ is a `CappedBaseStock.DemandLaw` and the demand path is distributed as its infinite product.
--   3. **State.** At the start of period $t$ the state is $x_t=(x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the inventory whose remaining lifetime is at most $i$ periods (a cumulative level). The firm orders $q_t\ge 0$ and raises the total level to $x_{t,m}=x_{t,m-1}+q_t$, with $x_{t,0}:=0$. The system starts empty, $x_1=0$.
--   4. **FIFO dynamics (1).** The outdated quantity is $o_t=(x_{t,1}-D_t)^+$ and
--   $$
--   x_{t+1,i}=(x_{t,i+1}-D_t-o_t)^+,\qquad i=1,\dots,m-1 .
--   $$
--   5. **Period cost (2).** $C^\pi_t=h(x^\pi_{t,m}-D_t)^++p(D_t-x^\pi_{t,m})^++\theta o^\pi_t$.
--   6. **Admissible policies.** A policy $\pi\in\Pi$ orders, in each period $t$, the quantity $\varphi^\pi_t(x_t)$ given by a non-negative measurable function of the current state. Its long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$, and $\mathrm{OPT}=\inf_{\pi\in\Pi}C^\pi$.
--   7. **Base-stock policy.** $\pi_S$ orders $q_t=(S-x_{t,m-1})^+$, raising the total level to $S$; $C(S)$ is its long-run average cost.
--   8. **Newsvendor level.** $S^{NP}=F^{-1}(p/(p+h))$ with $F^{-1}(x)=\inf\{y:F(y)\ge x\}$.
--
--   Together with the heuristic level $\widetilde S$ (any minimizer over $[0,\infty)$ of $\widetilde C(S)=h\,\mathbb E[(S-D)^+]+p\,\mathbb E[(D-S)^+]+\frac{\theta}{m}\,\mathbb E[(S-\sum_{i=1}^m D_i)^+]$, (4), defined in `PerishBaseStock.Lifetime.Model`), these are the objects compared in every optimality-gap bound of the paper; in this mission they are evaluated at the demand law of the population form (7).
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$. Levels live in $[0,\infty)$ and truncated subtraction is the positive part. The state is `Fin (m - 1) → ℝ≥0`, empty when $m=1$; then $x_{t,1}=x_{t,m}=q_t$ and $o_t=(q_t-D_t)^+$. Expectations of costs are lower Lebesgue integrals in $[0,\infty]$, and $C^\pi$ averages over $T+1$ periods, which has the same limsup. The parameters $(m,h,p,\theta)$ with their standing assumptions are the structure `PerishBaseStock.Lifetime.Params`, and the heuristic cost $\widetilde C$ of (4) with the minimizer predicate for $\widetilde S$ are `PerishBaseStock.Lifetime.heuristicCost` and `PerishBaseStock.Lifetime.IsHeuristicLevel`, both imported from `PerishBaseStock.Lifetime.Model`; this file adds the $\mathbb R_{\ge0}$-valued state, dynamics, costs and base-stock policy. $S^{NP}$ is the published `newsvendorLevel`. The base-stock policy is shown admissible (its order rule is measurable).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–10, §2, (1), (2), (4)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_PerishBaseStock_Lifetime_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-!
# The FIFO perishable inventory system with zero lead time (Bu, Gong & Chao, §2, pp. 8–10)

Time is zero-based: Lean period `t` is the paper's period `t + 1`, and the demand `d t` of a
demand path `d : CappedBaseStock.DemandPath` is the paper's `D_{t+1}`. The demands are i.i.d. with
law `P.law` under `CappedBaseStock.demandPathLaw P`.

The state `x : State m` holds the paper's *cumulative* levels `x_{t,1} ≤ ⋯ ≤ x_{t,m-1}`:
`x ⟨i - 1, _⟩` is `x_{t,i}`, the stock whose remaining lifetime is at most `i` periods. All levels
are in `ℝ≥0`; truncated subtraction on `ℝ≥0` is the paper's positive part `(·)⁺`.
-/

/-- The system state `(x_{t,1}, …, x_{t,m-1})`; empty (`Fin 0`) when `m = 1`. -/
abbrev State (m : ℕ) := Fin (m - 1) → ℝ≥0

/-- The empty initial state `x_1 = 0` (p. 8). -/
def emptyState (m : ℕ) : State m := fun _ => 0

/-- `x_{t,m-1}`, the total on-hand stock before ordering, with the convention `x_{t,0} := 0` when
`m = 1`. -/
def topLevel {m : ℕ} (x : State m) : ℝ≥0 :=
  if h : 0 < m - 1 then x ⟨m - 2, by omega⟩ else 0

/-- The cumulative level `x_{t,i}` for `i = 0, 1, …, m`, after an order `q`:
`x_{t,0} = 0`, `x_{t,i}` from the state for `1 ≤ i ≤ m - 1`, and the order-up-to level
`x_{t,m} = x_{t,m-1} + q` for `i ≥ m`. -/
def level {m : ℕ} (x : State m) (q : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if hi : i < m then (if h1 : 1 ≤ i then x ⟨i - 1, by omega⟩ else 0) else topLevel x + q

/-- Outdating in the period, `o_t = (x_{t,1} - D_t)⁺` (p. 8). When `m = 1`, `x_{t,1} = x_{t,m}`. -/
def outdate {m : ℕ} (x : State m) (q d : ℝ≥0) : ℝ≥0 :=
  level x q 1 - d

/-- The FIFO dynamics (1), p. 8: `x_{t+1,i} = (x_{t,i+1} - D_t - o_t)⁺`, `i = 1, …, m - 1`
(the Lean index `i` is the paper's `i + 1`). -/
def next {m : ℕ} (x : State m) (q d : ℝ≥0) : State m :=
  fun i => level x q (i.val + 2) - d - outdate x q d

/-- The period cost (2), p. 9: `h (x_{t,m} - D_t)⁺ + p (D_t - x_{t,m})⁺ + θ o_t`. -/
def periodCost (c : PerishBaseStock.Lifetime.Params) (x : State c.m) (q d : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal c.h * ((level x q c.m - d : ℝ≥0) : ℝ≥0∞) +
    ENNReal.ofReal c.p * ((d - level x q c.m : ℝ≥0) : ℝ≥0∞) +
    ENNReal.ofReal c.θ * ((outdate x q d : ℝ≥0) : ℝ≥0∞)

/-- Admissible policies Π (p. 9): in each period `t` the order is a non-negative measurable
function `φ_t(x_t)` of the current state. -/
structure Policy (m : ℕ) where
  φ : ℕ → State m → ℝ≥0
  measurable_φ : ∀ t, Measurable (φ t)

/-- The state trajectory under `π` along a demand path, from the empty state. -/
def run {m : ℕ} (π : Policy m) (d : CappedBaseStock.DemandPath) : ℕ → State m
  | 0 => emptyState m
  | t + 1 => next (run π d t) (π.φ t (run π d t)) (d t)

/-- `C^π_t`, the cost of period `t` under `π`. -/
def policyPeriodCost (c : PerishBaseStock.Lifetime.Params) (π : Policy c.m) (t : ℕ) (d : CappedBaseStock.DemandPath) :
    ℝ≥0∞ :=
  periodCost c (run π d t) (π.φ t (run π d t)) (d t)

/-- The long-run average cost `C^π = limsup_T (1/T) Σ_{t=1}^T E[C^π_t]` (p. 9), with lower
Lebesgue expectations in `ℝ≥0∞`. Averaging over `T + 1` periods has the same limsup. -/
def policyCost (P : CappedBaseStock.DemandLaw) (c : PerishBaseStock.Lifetime.Params) (π : Policy c.m) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1),
        ∫⁻ d, policyPeriodCost c π t d ∂CappedBaseStock.demandPathLaw P) /
      (T + 1 : ℝ≥0∞)) Filter.atTop

/-- The optimal cost `OPT = inf_{π ∈ Π} C^π` (p. 9), over all admissible policies. -/
def OPT (P : CappedBaseStock.DemandLaw) (c : PerishBaseStock.Lifetime.Params) : ℝ≥0∞ :=
  ⨅ π : Policy c.m, policyCost P c π

lemma measurable_topLevel (m : ℕ) : Measurable (fun x : State m => topLevel x) := by
  unfold topLevel
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The base-stock policy `π_S` (p. 9): order `q_t = (S - x_{t,m-1})⁺` in every period. -/
def baseStockPolicy (m : ℕ) (S : ℝ≥0) : Policy m where
  φ _ x := S - topLevel x
  measurable_φ _ := measurable_const.sub (measurable_topLevel m)

/-- `C(S)`, the long-run average cost of the base-stock policy `π_S` (p. 9). -/
def baseStockCost (P : CappedBaseStock.DemandLaw) (c : PerishBaseStock.Lifetime.Params) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost P c (baseStockPolicy c.m S)

/-- `S^NP = F^{-1}(p/(p+h))` (p. 10). -/
def newsvendorLevel (P : CappedBaseStock.DemandLaw) (c : PerishBaseStock.Lifetime.Params) : ℝ≥0 :=
  LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law c.h c.p

end PerishBaseStock.Population


