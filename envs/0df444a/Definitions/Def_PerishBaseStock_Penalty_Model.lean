-- Prove2me | Definitions.Def_PerishBaseStock_Penalty_Model
-- name    : PerishBaseStock_Penalty_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:06.32723+00:00
-- url     : https://prove2.me/theorems/c6fb4281-dff9-4ecf-b647-612ac70b3be5
-- title:
--   Lost-sales FIFO perishable inventory system with zero lead time: costs, policies, $\mathrm{OPT}$, $C(S)$, $\widetilde S$, $\underline S$, $\bar D$
-- statement:
--   This definition sets up the periodic-review perishable inventory system of Bu, Gong & Chao (§2), with lost sales, zero lead time and FIFO issuance, together with every quantity used by the large-penalty analysis.
--
--   **Data.** A product has a fixed lifetime of $m\ge 1$ periods. Demands $D_1,D_2,\dots$ are i.i.d. copies of a non-negative random variable $D$ with $0<\mathbb E[D]<\infty$ and distribution function $F(x)=\mathbb P(D\le x)$. The unit holding cost is $h>0$, the unit lost-sales penalty $p>0$ and the additional unit outdating cost $\theta\ge 0$.
--
--   **State and dynamics.** At the start of period $t$ the state is $x_t=(x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the stock whose remaining lifetime is at most $i$ periods (with $x_{t,0}:=0$). The firm orders $q_t\ge 0$ and raises the total level to $x_{t,m}=x_{t,m-1}+q_t$. Demand is served oldest first; unmet demand is lost. The outdated quantity is $o_t=(x_{t,1}-D_t)^+$ and
--
--   $$x_{t+1,i}=(x_{t,i+1}-D_t-o_t)^+,\qquad i=1,\dots,m-1. \quad (1)$$
--
--   The system starts empty, $x_1=0$.
--
--   **Policies and costs.** An admissible policy $\pi$ orders $q_t=\varphi^\pi_t(x_t)$ with each $\varphi^\pi_t$ a non-negative measurable function of the current state; $\Pi$ is the set of all such policies. The period cost is $C^\pi_t=h(x^\pi_{t,m}-D_t)^++p(D_t-x^\pi_{t,m})^++\theta o^\pi_t$, the long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$, and $\mathrm{OPT}=\inf_{\pi\in\Pi}C^\pi$.
--
--   **Base-stock policies.** The base-stock policy $\pi_S$ orders $(S-x_{t,m-1})^+$; $C(S)$ is its long-run average cost and $\mathbb E[O_\infty(S)]$ its long-run average outdated quantity, $\limsup_T\frac1T\sum_{t=1}^T\mathbb E[o^{\pi_S}_t]$.
--
--   **Levels.** The heuristic cost is
--
--   $$\widetilde C(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big],\quad (4)$$
--
--   and $\widetilde S$ denotes any minimizer of $\widetilde C$ over $[0,\infty)$. The floor level $\underline S$ is the least minimizer over $S\ge 0$ of $h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta S$. The upper support is $\bar D=\sup\{x:F(x)<1\}\in[0,\infty]$, and demand is bounded when $\bar D<\infty$.
--
--   These objects are the common vocabulary of Theorem 3 and its milestones.
--
--   **Formalization Note** The parameters $(m,h,p,\theta)$ are a plain record; the standing assumptions $m\ge1$, $h>0$, $p>0$, $\theta\ge0$ of p. 8 are the separate predicate `Params.Standing`, which every statement using this model must assume (this lets $p$ vary in the limit $p\to\infty$). Time is zero-based: Lean period $t$ is the paper's period $t+1$ and `d t` is $D_{t+1}$. The state is `Fin (m - 1) → ℝ` of cumulative levels. Costs, expectations (lower Lebesgue integrals over the i.i.d. path law) and long-run averages live in $[0,\infty]$; the average is taken over horizons $T+1$, which has the same limsup. $\mathbb E[O_\infty(S)]$ is rendered by its defining long-run average from the empty state. $\underline S$ is the infimum of the set of minimizers, which is the least minimizer because that set is nonempty and closed; the paper writes $\arg\min$ without saying which minimizer, and the least one is chosen. $\bar D$ is computed over $x\ge 0$, which gives the same value since $F(x)=0<1$ for $x<0$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–10, §2, (1), (2), (4); p. 13, D̄; p. 22, Proposition 3 (S̲); p. 9, Lemma 1 (E[O∞(S)])

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
noncomputable section

/-!
# The lost-sales FIFO perishable inventory system with zero lead time (Bu, Gong & Chao, §2)

Time is zero-based: Lean period `t` is the paper's period `t + 1`, and `d t` is the
paper's `D_{t+1}`. The state `x : Fin (m - 1) → ℝ` holds the paper's cumulative levels
`(x_{t,1}, …, x_{t,m-1})`: coordinate `j` is `x_{t,j+1}`, the stock whose remaining
lifetime is at most `j + 1` periods. The system starts empty. Costs are in `ℝ≥0∞`,
expectations are lower Lebesgue integrals over the i.i.d. demand path law, and the
long-run average is the limsup of Cesàro averages.
-/

namespace PerishBaseStock.Penalty

/-- Model parameters: lifetime `m`, unit holding cost `h`, unit lost-sales penalty `p`,
and unit outdating cost `θ`. The standing assumptions are `Params.Standing`. -/
structure Params where
  m : ℕ
  h : ℝ
  p : ℝ
  θ : ℝ

/-- The standing assumptions of p. 8: `m ≥ 1`, `h > 0`, `p > 0`, `θ ≥ 0`. -/
structure Params.Standing (c : Params) : Prop where
  one_le_m : 1 ≤ c.m
  h_pos : 0 < c.h
  p_pos : 0 < c.p
  θ_nonneg : 0 ≤ c.θ

/-- The paper's level `x_{t,i}` for `i = 0, 1, …, m` given the state and the order `q`:
`x_{t,0} = 0`, `x_{t,i}` for `1 ≤ i ≤ m - 1` from the state, and
`x_{t,m} = x_{t,m-1} + q` for `i ≥ m`. -/
def level {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) (i : ℕ) : ℝ :=
  if h0 : i = 0 then 0
  else if hi : i < m then x ⟨i - 1, by omega⟩
  else PerishBaseStock.Lifetime.topLevel x + q

/-- PerishBaseStock.Lifetime.State trajectory from the empty state along the demand path `d`. -/
def run {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) : ℕ → PerishBaseStock.Lifetime.State m
  | 0 => PerishBaseStock.Lifetime.emptyState m
  | t + 1 => PerishBaseStock.Lifetime.step (run π d t) (π.φ t (run π d t)) (d t)

/-- The order `q_t = φ_t(x_t)` placed in period `t`. -/
def orderQty {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ≥0 :=
  π.φ t (run π d t)

/-- `x^π_{t,m}` along the path `d`. -/
def totalLevel {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  PerishBaseStock.Lifetime.orderUpTo (run π d t) (orderQty π d t)

/-- `o^π_t` along the path `d`. -/
def outdated {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  PerishBaseStock.Lifetime.outdate (run π d t) (orderQty π d t) (d t)

/-- Period cost (2): `h (x_{t,m} - D_t)^+ + p (D_t - x_{t,m})^+ + θ o_t`. -/
def periodCost (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ℝ≥0∞ :=
  ENNReal.ofReal c.h * ENNReal.ofReal (max (totalLevel π d t - d t) 0) +
    ENNReal.ofReal c.p * ENNReal.ofReal (max ((d t : ℝ) - totalLevel π d t) 0) +
    ENNReal.ofReal c.θ * ENNReal.ofReal (outdated π d t)

/-- `limsup_{T→∞} (1/T) Σ_{t=1}^T E[X_t]` for a non-negative process (index shifted to
zero-based time; horizon `T + 1`). -/
def longRunAverage (P : CappedBaseStock.DemandLaw)
    (X : ℕ → CappedBaseStock.DemandPath → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1), ∫⁻ d, X t d ∂CappedBaseStock.demandPathLaw P) /
      ((T : ℝ≥0∞) + 1)) Filter.atTop

/-- Long-run average cost `C^π`. -/
def policyCost (c : Params) (P : CappedBaseStock.DemandLaw) (π : PerishBaseStock.Lifetime.Policy c.m) : ℝ≥0∞ :=
  longRunAverage P (fun t d => periodCost c π d t)

/-- Optimal long-run average cost `OPT = inf_{π ∈ Π} C^π`. -/
def OPT (c : Params) (P : CappedBaseStock.DemandLaw) : ℝ≥0∞ :=
  ⨅ π : PerishBaseStock.Lifetime.Policy c.m, policyCost c P π

lemma measurable_topLevel (m : ℕ) : Measurable (fun x : PerishBaseStock.Lifetime.State m => PerishBaseStock.Lifetime.topLevel x) := by
  unfold PerishBaseStock.Lifetime.topLevel
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The base-stock policy `π_S`: order `q_t = (S - x_{t,m-1})^+`. -/
def baseStockPolicy (m : ℕ) (S : ℝ≥0) : PerishBaseStock.Lifetime.Policy m where
  φ _ x := Real.toNNReal ((S : ℝ) - PerishBaseStock.Lifetime.topLevel x)
  measurable_φ _ := measurable_real_toNNReal.comp
    (measurable_const.sub (measurable_topLevel m))

/-- `C(S)`, the long-run average cost of `π_S`. -/
def baseStockCost (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost c P (baseStockPolicy c.m S)

/-- `E[O∞(S)]`, the long-run average outdating of `π_S` from the empty state. -/
def avgOutdating (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) : ℝ≥0∞ :=
  longRunAverage P (fun t d => ENNReal.ofReal (outdated (baseStockPolicy c.m S) d t))

/-- `D̄ = sup{x : F(x) < 1}` in `[0, ∞]`, where `F(x) = P(D ≤ x)`. -/
def upperSupport (P : CappedBaseStock.DemandLaw) : ℝ≥0∞ :=
  ⨆ (x : ℝ≥0) (_ : P.law (Set.Iic x) < 1), (x : ℝ≥0∞)

/-- "Demand `D` is bounded": `D̄ < ∞`. -/
def DemandBounded (P : CappedBaseStock.DemandLaw) : Prop := upperSupport P < ⊤

/-- The heuristic cost (4):
`C̃(S) = h E[(S - D)^+] + p E[(D - S)^+] + (θ/m) E[(S - Σ_{i=1}^m D_i)^+]`. -/
def heuristicCost (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.p S +
    c.θ / (c.m : ℝ) *
      LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S

/-- `S̃` is a minimizer of `C̃` over `[0, +∞)`. -/
def IsHeuristicLevel (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, heuristicCost c P S ≤ heuristicCost c P S'

/-- The function `h E[(S - D)^+] + p E[(D - S)^+] + θ S` of Proposition 3. -/
def floorCost (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.p S + c.θ * S

/-- `S̲ = argmin_{S ≥ 0} {h E[(S - D)^+] + p E[(D - S)^+] + θ S}`, taken to be the least
minimizer (the infimum of the set of minimizers). -/
def floorLevel (c : Params) (P : CappedBaseStock.DemandLaw) : ℝ≥0 :=
  sInf {S : ℝ≥0 | ∀ S' : ℝ≥0, floorCost c P S ≤ floorCost c P S'}

end PerishBaseStock.Penalty


