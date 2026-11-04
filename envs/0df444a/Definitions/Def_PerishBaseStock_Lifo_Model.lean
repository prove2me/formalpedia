-- Prove2me | Definitions.Def_PerishBaseStock_Lifo_Model
-- name    : PerishBaseStock_Lifo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:07.789182+00:00
-- url     : https://prove2.me/theorems/07fb245a-6d4d-4a21-ae2d-32562aecf381
-- title:
--   §2 and §4.1 — the perishable lost-sales inventory system under LIFO issuance: dynamics, admissible policies, $C^\pi$, OPT, $\pi_S$, $C(S)$, $\underline D$
-- statement:
--   This file sets up the periodic-review inventory system of a perishable product with lost sales, zero lead time and **last-in-first-out (LIFO)** issuance, as in Bu, Gong and Chao (§2 and §4.1).
--
--   **Demand.** The demands $D_1, D_2, \dots$ are i.i.d. copies of a nonnegative random variable $D$ with $0<\mathbb E[D]<\infty$ and distribution function $F(x)=\mathbb P(D\le x)$ (the published demand layer `CappedBaseStock.DemandLaw`).
--
--   **Parameters.** The product has lifetime $m\ge 1$ periods; leftover inventory costs $h>0$ per unit, a lost sale costs $p>0$ per unit, and outdated inventory costs an additional $\theta\ge 0$ per unit.
--
--   **State and dynamics.** At the start of period $t$ the state is $x_t=(x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the inventory whose remaining lifetime is at most $i$ periods; $x_{t,0}:=0$. The firm orders $q_t\ge 0$, raising the total level to $x_{t,m}=x_{t,m-1}+q_t$. Demand $D_t$ is served newest-first, and the outdated amount and the next state are
--   $$o_t=\min\{(x_{t,m}-D_t)^+,\,x_{t,1}\},\qquad x_{t+1,i}=\min\{(x_{t,m}-D_t)^+,\,x_{t,i+1}\}-o_t,\quad i=1,\dots,m-1.$$
--   The system starts empty, $x_1=0$.
--
--   **Policies and costs.** A policy $\pi$ is *admissible* if its order in each period $t$ is a nonnegative measurable function $\phi^\pi_t(x_t)$ of the current state; $\Pi$ is the set of admissible policies. The period cost is
--   $$C^\pi_t=h(x^\pi_{t,m}-D_t)^++p(D_t-x^\pi_{t,m})^++\theta o^\pi_t,$$
--   the long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$, and $\mathrm{OPT}^{LIFO}=\inf_{\pi\in\Pi}C^\pi$. The base-stock policy $\pi_S$ ($S\ge 0$) orders $(S-x_{t,m-1})^+$ in every period, and $C^{LIFO}(S)=C^{\pi_S}$.
--
--   **Demand support.** The lower support is $\underline D=\inf\{x:F(x)>0\}$, and demand is *unbounded* when $F(x)<1$ for every $x$.
--
--   These objects are the model of every statement in this mission.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$ and `d t` is $D_{t+1}$. The state is `Fin (m - 1) → ℝ` holding the cumulative levels; `cum x 0 = 0` and `level x q m` is $x_{t,m}$, so $m=1$ (empty state, $x_{t,1}=x_{t,m}=q_t$) is included. Costs live in $[0,\infty]$, expectations are lower Lebesgue integrals over the i.i.d. path law, and the average uses horizons $T+1$, $T\in\mathbb N$, which has the same limsup. The standing assumptions $m\ge1$, $h>0$, $p>0$, $\theta\ge0$ are the predicate `Params.Standing`, separate from the parameter record so that one parameter can be varied in limit statements.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–9, §2 (1)–(2); p. 15, D̲; p. 16, §4.1 LIFO dynamics

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_PerishBaseStock_Lifetime_Model

/-!
# Perishable lost-sales inventory under LIFO issuance (Bu, Gong & Chao, §2 and §4.1)

Time is zero-based: Lean period `t` is the paper's period `t + 1`, and the demand `d t`
is the paper's `D_{t+1}`. The state `x : Fin (m - 1) → ℝ` holds the paper's *cumulative*
levels `x_{t,1}, …, x_{t,m-1}`: `x ⟨i - 1, _⟩` is the stock whose remaining lifetime is at
most `i` periods. `cum x 0 = 0` is the paper's convention `x_{t,0} := 0`. The system starts
empty. Costs are in `ℝ≥0∞`; expectations are lower Lebesgue integrals over the i.i.d.
demand path law, so no integrability side condition can make a cost vanish.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifo

/-- Model parameters: the lifetime `m`, the unit holding cost `h`, the unit lost-sales
penalty `p` and the additional unit outdating cost `θ`. The standing assumptions of the
paper are collected separately in `Params.Standing`, so that one parameter can be varied
by record update. -/
structure Params where
  m : ℕ
  h : ℝ
  p : ℝ
  θ : ℝ

/-- The paper's standing assumptions (p. 8): `m ≥ 1`, `h > 0`, `p > 0`, `θ ≥ 0`. -/
structure Params.Standing (c : Params) : Prop where
  one_le_m : 1 ≤ c.m
  h_pos : 0 < c.h
  p_pos : 0 < c.p
  θ_nonneg : 0 ≤ c.θ

/-- Cumulative level `x_{t,i}` for `0 ≤ i ≤ m - 1`, with `x_{t,0} = 0` (and `0` beyond). -/
def cum {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (i : ℕ) : ℝ :=
  if hi : 0 < i ∧ i < m then x ⟨i - 1, by omega⟩ else 0

/-- Cumulative level `x_{t,i}` for `0 ≤ i ≤ m` after ordering `q`: for `i < m` it is the
state's level, and `x_{t,m} = x_{t,m-1} + q` is the order-up-to level. -/
def level {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ) (i : ℕ) : ℝ :=
  if i < m then cum x i else cum x (m - 1) + q

/-- Leftover inventory `(x_{t,m} - D_t)⁺` after demand is served. -/
def leftover {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q d : ℝ) : ℝ :=
  max (level x q m - d) 0

/-- LIFO outdating `o_t = min{(x_{t,m} - D_t)⁺, x_{t,1}}` (p. 16). For `m = 1`,
`x_{t,1} = x_{t,m}`. -/
def outdate {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q d : ℝ) : ℝ :=
  min (leftover x q d) (level x q 1)

/-- LIFO dynamics (p. 16): `x_{t+1,i} = min{(x_{t,m} - D_t)⁺, x_{t,i+1}} - o_t`,
`i = 1, …, m - 1`; the entry `j : Fin (m - 1)` is `i = j + 1`. -/
def lifoStep {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q d : ℝ) : PerishBaseStock.Lifetime.State m :=
  fun j => min (leftover x q d) (level x q (j.val + 2)) - outdate x q d

/-- The LIFO trajectory of policy `π` from the empty state `x_1 = 0` (p. 8) along the demand
path `d`: `x_{t+1} = lifoStep x_t (φ_t(x_t)) D_t`. -/
def run {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) :
    ℕ → PerishBaseStock.Lifetime.State m
  | 0 => PerishBaseStock.Lifetime.emptyState m
  | t + 1 => lifoStep (run π d t) (π.φ t (run π d t) : ℝ) (d t : ℝ)

/-- The order-up-to level `x^π_{t,m}`. -/
def orderUpTo {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  level (run π d t) (π.φ t (run π d t) : ℝ) m

/-- The outdated quantity `o^π_t`. -/
def outdated {m : ℕ} (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  outdate (run π d t) (π.φ t (run π d t) : ℝ) (d t : ℝ)

/-- The period cost (2): `C^π_t = h(x_{t,m} - D_t)⁺ + p(D_t - x_{t,m})⁺ + θ o_t`. -/
def periodCost (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (orderUpTo π d t - d t) 0) +
    ENNReal.ofReal (c.p * max ((d t : ℝ) - orderUpTo π d t) 0) +
    ENNReal.ofReal (c.θ * outdated π d t)

/-- Long-run average cost `C^π = limsup_T (1/T) Σ_{t=1}^T E[C^π_t]` (horizon `T + 1`,
`T ∈ ℕ`, which has the same limsup). -/
def policyCost (P : CappedBaseStock.DemandLaw) (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1),
        ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P) /
      ((T : ℝ≥0∞) + 1)) Filter.atTop

/-- The optimal cost `OPT^{LIFO} = inf_{π ∈ Π} C^π` over all admissible policies. -/
def OPT (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ≥0∞ :=
  ⨅ π : PerishBaseStock.Lifetime.Policy c.m, policyCost P c π

lemma measurable_baseStockRule (m : ℕ) (S : ℝ≥0) :
    Measurable (fun x : PerishBaseStock.Lifetime.State m => Real.toNNReal ((S : ℝ) - cum x (m - 1))) := by
  unfold cum
  split_ifs <;> fun_prop

/-- The base-stock policy `π_S` (p. 9): order `q_t = (S - x_{t,m-1})⁺`. -/
def baseStock (m : ℕ) (S : ℝ≥0) : PerishBaseStock.Lifetime.Policy m where
  φ _ x := Real.toNNReal ((S : ℝ) - cum x (m - 1))
  measurable_φ _ := measurable_baseStockRule m S

/-- `C^{LIFO}(S)`, the long-run average cost of `π_S`. -/
def baseStockCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost P c (baseStock c.m S)

/-- The demand lower support `D̲ = inf{x : F(x) > 0}` (p. 15). Demand is nonnegative, so
the infimum over `ℝ` equals the infimum over `ℝ≥0`, and the set is nonempty. -/
def lowerSupport (P : CappedBaseStock.DemandLaw) : ℝ≥0 :=
  sInf {x : ℝ≥0 | 0 < P.law (Set.Iic x)}

/-- Demand is unbounded: `F(x) < 1` for every `x`, i.e. `D̄ = sup{x : F(x) < 1} = ∞`. -/
def DemandUnbounded (P : CappedBaseStock.DemandLaw) : Prop :=
  ∀ x : ℝ≥0, P.law (Set.Iic x) < 1

end PerishBaseStock.Lifo


