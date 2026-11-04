-- Prove2me | Definitions.Def_PerishBaseStock_LifoNegative_Model
-- name    : PerishBaseStock_LifoNegative_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T04:27:45.828343+00:00
-- url     : https://prove2.me/theorems/711160d4-12d4-4ea8-9cb4-a629daf13b10
-- title:
--   Perishable lost-sales inventory under LIFO issuance: dynamics, admissible policies, $C^{LIFO}$, $\mathrm{OPT}^{LIFO}$, $\underline D$, $\hat C_L$ and the cyclic policy
-- statement:
--   This file sets up the perishable inventory system of Bu, Gong and Chao under the **last-in-first-out (LIFO)** issuance policy, with lost sales and zero lead time.
--
--   **Demand and parameters.** Demands $D_1, D_2, \dots$ are i.i.d. copies of a nonnegative random variable $D$ with $0 < \mathbb E[D] < \infty$ and distribution function $F(x) = \mathbb P(D \le x)$. The product has a lifetime of $m \ge 1$ periods; the unit holding cost is $h > 0$, the unit lost-sales penalty $p > 0$ and the unit outdating cost $\theta \ge 0$. The **demand lower support** is
--   $$\underline D = \inf\{x \in \mathbb R : F(x) > 0\},$$
--   and the newsvendor level is $S^{NP} = F^{-1}(p/(p+h))$ with $F^{-1}(x) = \inf\{y : F(y) \ge x\}$.
--
--   **State and LIFO dynamics.** The state at the start of period $t$ is $x_t = (x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the stock whose remaining lifetime is at most $i$ periods (cumulative levels; $x_{t,0} := 0$). After an order $q_t \ge 0$ the total level is $x_{t,m} = x_{t,m-1} + q_t$. Demand is served youngest stock first, and
--   $$o_t = \min\{(x_{t,m} - D_t)^+, x_{t,1}\}, \qquad x_{t+1,i} = \min\{(x_{t,m} - D_t)^+, x_{t,i+1}\} - o_t,\quad i = 1,\dots,m-1.$$
--   The system starts empty, $x_1 = 0$.
--
--   **Costs and policies.** The cost of period $t$ is $C^\pi_t = h(x_{t,m} - D_t)^+ + p(D_t - x_{t,m})^+ + \theta o_t$. A policy is **admissible** if its order in period $t$ is a nonnegative measurable function $\varphi_t(x_t)$ of the current state; $\Pi$ is the set of admissible policies. The long-run average cost is
--   $$C^\pi = \limsup_{T\to\infty} \frac1T \sum_{t=1}^T \mathbb E[C^\pi_t], \qquad \mathrm{OPT}^{LIFO} = \inf_{\pi\in\Pi} C^\pi.$$
--   The base-stock policy $\pi_S$ orders $(S - x_{t,m-1})^+$; its cost is $C^{LIFO}(S)$, and the best base-stock cost is $\inf_{S \ge 0} C^{LIFO}(S)$, written $C^{LIFO}(S^{LIFO,*})$ in the paper.
--
--   **The lower-bound function (11).**
--   $$\hat C_L(S) = h\mathbb E[(S-D)^+] + p\mathbb E[(D-S)^+] + \frac{\theta}{m}\mathbb E[(S - \max\{D_1,\dots,D_m\})^+].$$
--
--   **The cyclic policy of Appendix C.3.** Order $\min\{S^{NP}, m\underline D\}$ units in periods $1, m+1, 2m+1, \dots$, and use the base-stock policy with level $\underline D$ in all other periods.
--
--   These objects are the vocabulary of Proposition 1 and its proof: the best base-stock policy stays a positive distance from optimal as $\theta\to\infty$ when $m\ge 2$ and $S^{NP} > \underline D > 0$.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$ and `d t` is $D_{t+1}$; the cyclic policy's periods $1, m+1, \dots$ are the Lean periods $t$ with $t \bmod m = 0$. The state is `Fin (m - 1) → ℝ`, so $m = 1$ is the empty state. Period costs take values in $[0,\infty]$, expectations are lower Lebesgue integrals over the i.i.d. demand path law, and the average uses the horizons $T+1$ (same limsup). `Params.withTheta c θ` is the same system with outdating cost $\theta \ge 0$; limits in $\theta$ are taken along $\theta \in [0,\infty)$. Demand law, `mean`, the newsvendor cost `backorderCost` and `newsvendorLevel` come from the published definitions `CappedBaseStock_Model` and `LostSalesOrderUpTo.Asymptotic.Backorder`; `newsvendorLevel` is $\inf\{S \ge 0 : p/(p+h) \le F(S)\}$, which equals $F^{-1}(p/(p+h))$ because $F = 0$ on $(-\infty,0)$ and $p/(p+h) \in (0,1)$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–10 (model, (2), Π, C^π, OPT, π_S), p. 15 (D̲), p. 16 (LIFO dynamics, (11)), pp. ec8–ec9 (cyclic policy of App. C.3)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_PerishBaseStock_Lifetime_Model
import Definitions.Def_PerishBaseStock_Outdating_Heuristic

/-!
# Perishable inventory under LIFO issuance (Bu, Gong & Chao, §2 and §4.1)

Lost-sales periodic-review system of a product with lifetime `m`, zero lead time and LIFO
issuance (p. 16), started empty (p. 8). Time is zero-based: Lean period `t` is the paper's
period `t + 1`, and `d t` is the paper's demand `D_{t+1}`. The state `x : Fin (m - 1) → ℝ`
holds the *cumulative* levels: `x ⟨i - 1, _⟩` is the paper's `x_{t,i}`, the stock with
remaining lifetime at most `i`, `1 ≤ i ≤ m - 1`; `stockLevel x 0 = 0` is the convention
`x_{t,0} = 0`. Costs are in `ℝ≥0∞` and expectations are lower Lebesgue integrals, so no
integrability fallback can lower a cost.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.LifoNegative

open CappedBaseStock LostSalesOrderUpTo.Asymptotic

/-- Model parameters (p. 8): lifetime `m ≥ 1`, unit holding cost `h > 0`, unit lost-sales
penalty `p > 0`, unit outdating cost `θ ≥ 0`. -/
structure Params where
  m : ℕ
  h : ℝ
  p : ℝ
  θ : ℝ
  one_le_m : 1 ≤ m
  h_pos : 0 < h
  p_pos : 0 < p
  θ_nonneg : 0 ≤ θ

/-- The same system with outdating cost `θ` (all other parameters unchanged). -/
def Params.withTheta (c : Params) (θ : ℝ≥0) : Params :=
  { c with θ := (θ : ℝ), θ_nonneg := θ.2 }

/-- `x_{t,i}` for `0 ≤ i ≤ m - 1`, with `x_{t,0} = 0` (and `0` beyond the state). -/
def stockLevel {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (i : ℕ) : ℝ :=
  if hi : 0 < i ∧ i < m then x ⟨i - 1, by omega⟩ else 0

/-- The order-up-to level `x_{t,m} = x_{t,m-1} + q_t` after ordering `q`. -/
def orderUpTo {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) : ℝ :=
  stockLevel x (m - 1) + (q : ℝ)

/-- `x_{t,i}` for `1 ≤ i ≤ m`, the top level `x_{t,m}` including the new order. -/
def level {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) (i : ℕ) : ℝ :=
  if i < m then stockLevel x i else orderUpTo x q

/-- LIFO outdating (p. 16): `o_t = min{(x_{t,m} - D_t)⁺, x_{t,1}}`. -/
def outdating {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) (D : ℝ≥0) : ℝ :=
  min (max (orderUpTo x q - (D : ℝ)) 0) (level x q 1)

/-- LIFO dynamics (p. 16): `x_{t+1,i} = min{(x_{t,m} - D_t)⁺, x_{t,i+1}} - o_t`,
`i = 1, …, m - 1` (Lean index `i.val` is the paper's `i - 1`). -/
def lifoStep {m : ℕ} (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) (D : ℝ≥0) : PerishBaseStock.Lifetime.State m :=
  fun i => min (max (orderUpTo x q - (D : ℝ)) 0) (level x q (i.val + 2)) - outdating x q D

/-- Period cost (2): `h(x_{t,m} - D_t)⁺ + p(D_t - x_{t,m})⁺ + θ o_t`. -/
def periodCost (c : Params) (x : PerishBaseStock.Lifetime.State c.m) (q : ℝ≥0) (D : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (orderUpTo x q - (D : ℝ)) 0) +
    ENNReal.ofReal (c.p * max ((D : ℝ) - orderUpTo x q) 0) +
    ENNReal.ofReal (c.θ * outdating x q D)

/-- A (time-dependent, Markov) order rule: the order in period `t` is `φ t x_t ≥ 0`. -/
abbrev OrderRule (m : ℕ) := ℕ → PerishBaseStock.Lifetime.State m → ℝ≥0

/-- The state trajectory from the empty state along a demand path. -/
def run {m : ℕ} (φ : OrderRule m) (d : DemandPath) : ℕ → PerishBaseStock.Lifetime.State m
  | 0 => PerishBaseStock.Lifetime.emptyState m
  | t + 1 => lifoStep (run φ d t) (φ t (run φ d t)) (d t)

/-- The cost `C^π_t` incurred in (zero-based) period `t` along the demand path `d`. -/
def costAt (c : Params) (φ : OrderRule c.m) (d : DemandPath) (t : ℕ) : ℝ≥0∞ :=
  periodCost c (run φ d t) (φ t (run φ d t)) (d t)

/-- Long-run average cost `C^π = limsup_T (1/T) Σ_{t=1}^T E[C^π_t]` (p. 9). -/
def longRunCost (P : DemandLaw) (c : Params) (φ : OrderRule c.m) : ℝ≥0∞ :=
  limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1), ∫⁻ d, costAt c φ d t ∂demandPathLaw P) /
      ((T : ℝ≥0∞) + 1)) atTop

/-- Admissible policies Π (p. 9): the order in period `t` is a nonnegative measurable
function of the current state. -/
structure AdmissiblePolicy (m : ℕ) where
  φ : OrderRule m
  measurable_φ : ∀ t, Measurable (φ t)

/-- The optimal cost `OPT^{LIFO} = inf_{π ∈ Π} C^π`. -/
def OPT (P : DemandLaw) (c : Params) : ℝ≥0∞ :=
  ⨅ π : AdmissiblePolicy c.m, longRunCost P c π.φ

/-- Base-stock policy `π_S`: order `(S - x_{t,m-1})⁺` (p. 9). -/
def baseStockOrder {m : ℕ} (S : ℝ≥0) : OrderRule m :=
  fun _ x => Real.toNNReal ((S : ℝ) - stockLevel x (m - 1))

/-- `C^{LIFO}(S)`, the long-run average cost of `π_S`. -/
def baseStockCost (P : DemandLaw) (c : Params) (S : ℝ≥0) : ℝ≥0∞ :=
  longRunCost P c (baseStockOrder S)

/-- `C^{LIFO}(S^{LIFO,*}) := inf_{S ≥ 0} C^{LIFO}(S)`, the best base-stock cost. -/
def bestBaseStockCost (P : DemandLaw) (c : Params) : ℝ≥0∞ :=
  ⨅ S : ℝ≥0, baseStockCost P c S

/-- `E[(S - max{D_1, …, D_m})⁺]`. -/
def expectedHoldingMax (P : DemandLaw) (m : ℕ) (S : ℝ≥0) : ℝ :=
  ∫ d, max ((S : ℝ) - (((Finset.range m).sup d : ℝ≥0) : ℝ)) 0 ∂demandPathLaw P

/-- The lower bound (11): `Ĉ_L(S) = hE[(S-D)⁺] + pE[(D-S)⁺] + (θ/m)E[(S - max_i D_i)⁺]`. -/
def lowerBoundCost (P : DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  backorderCost P.law c.h c.p S + c.θ / (c.m : ℝ) * expectedHoldingMax P c.m S

/-- The cyclic policy of App. C.3 (ec8–ec9): order `min{S^NP, mD̲}` units in the paper's
periods `1, m+1, 2m+1, …` (Lean periods `t ≡ 0 mod m`), and use the base-stock policy with
level `D̲` in all other periods. -/
def cyclicOrder (P : DemandLaw) (c : Params) : OrderRule c.m :=
  fun t x =>
    if t % c.m = 0 then
      Real.toNNReal (min (newsvendorLevel P.law c.h c.p : ℝ) ((c.m : ℝ) * PerishBaseStock.Outdating.lowerSupport P))
    else Real.toNNReal (PerishBaseStock.Outdating.lowerSupport P - stockLevel x (c.m - 1))

end PerishBaseStock.LifoNegative


