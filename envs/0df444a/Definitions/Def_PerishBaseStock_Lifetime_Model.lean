-- Prove2me | Definitions.Def_PerishBaseStock_Lifetime_Model
-- name    : PerishBaseStock_Lifetime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:24.987764+00:00
-- url     : https://prove2.me/theorems/46d91ac2-e48f-40d8-a9a0-5635ad65a51b
-- title:
--   §2 — the perishable lost-sales inventory system under FIFO issuance: dynamics (1), cost (2), $\Pi$, OPT, $\pi_S$, $C(S)$, $\mathbb E[O_\infty(S)]$, $\widetilde C$ and $\widetilde S$
-- statement:
--   This file sets up the periodic-review inventory system of a perishable product with lost sales, zero lead time and **first-in-first-out (FIFO)** issuance of Bu, Gong and Chao (§2), together with the heuristic base-stock level of p. 10.
--
--   **Demand.** The demands $D_1, D_2, \dots$ are i.i.d. copies of a nonnegative random variable $D$ with $0<\mathbb E[D]<\infty$ and distribution function $F(x)=\mathbb P(D\le x)$ (the published demand layer `CappedBaseStock.DemandLaw` and its i.i.d. path law).
--
--   **Parameters.** The product has a fixed lifetime of $m\ge 1$ periods. Leftover inventory costs $h>0$ per unit, a lost sale costs $p>0$ per unit, and outdated inventory costs an additional $\theta\ge 0$ per unit.
--
--   **State and dynamics.** At the start of period $t$ the state is $\mathbf x_t=(x_{t,1},\dots,x_{t,m-1})$, where $x_{t,i}$ is the inventory whose remaining lifetime is at most $i$ periods (with $x_{t,0}:=0$). The firm orders $q_t\ge 0$ and raises the total level to $x_{t,m}=x_{t,m-1}+q_t$. Demand $D_t$ is served oldest-first; the outdated amount and the next state are
--   $$o_t=(x_{t,1}-D_t)^+,\qquad x_{t+1,i}=(x_{t,i+1}-D_t-o_t)^+,\quad i=1,\dots,m-1. \tag{1}$$
--   The system starts empty, $\mathbf x_1=0$. For $m=1$ the state is empty, $x_{t,1}=x_{t,m}=q_t$, and all leftover stock outdates.
--
--   **Policies and costs.** A policy $\pi$ is *admissible* if its order in each period $t$ is a nonnegative measurable function $\varphi^\pi_t(\mathbf x_t)$ of the current state; $\Pi$ is the set of admissible policies. The period cost is
--   $$C^\pi_t=h(x^\pi_{t,m}-D_t)^++p(D_t-x^\pi_{t,m})^++\theta o^\pi_t, \tag{2}$$
--   the long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$, and $\mathrm{OPT}=\inf_{\pi\in\Pi}C^\pi$.
--
--   **Base-stock policies.** For $S\ge 0$ the base-stock policy $\pi_S$ orders $q_t=(S-x_{t,m-1})^+$ in every period, and $C(S)=C^{\pi_S}$ is its long-run average cost from the empty state. The long-run average expected outdating of $\pi_S$,
--   $$\bar o(S)=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E\big[o^{\pi_S}_t\big],$$
--   is the quantity the paper writes $\mathbb E[O_\infty(S)]$. The file also records the state space $\mathcal X=\{0\le x_1\le\dots\le x_{m-1}\le S\}$ of $\pi_S$ and the averages $\frac1T\sum_{t\le T}\mathbb E[o^{\pi_S}_t]$ from an arbitrary initial state.
--
--   **Heuristic level.** With $S^{NP}=F^{-1}\big(\tfrac{p}{p+h}\big)$, $F^{-1}(x)=\inf\{y:F(y)\ge x\}$, the heuristic cost is
--   $$\widetilde C(S)=h\,\mathbb E[(S-D)^+]+p\,\mathbb E[(D-S)^+]+\frac{\theta}{m}\,\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big], \tag{4}$$
--   and $\widetilde S$ is any minimizer of $\widetilde C$ over $[0,+\infty)$.
--
--   These objects are the model of every statement in this mission.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$ and `d t` is $D_{t+1}$. The state is `Fin (m - 1) → ℝ` holding the cumulative levels, so $m=1$ (the empty state) is included. Costs live in $[0,\infty]$, expectations are lower Lebesgue integrals over the i.i.d. path law, and averages use horizons $T+1$, $T\in\mathbb N$, which has the same limsup. The trajectory is a recursion on the demand path, so the state of period $t$ depends on $D_1,\dots,D_{t-1}$ only. The newsvendor pieces $\mathbb E[(S-D)^+]$, $\mathbb E[(D-S)^+]$, $\mathbb E[(S-\sum_{i\le m}D_i)^+]$ and $F^{-1}(p/(p+h))$ are the published `expectedHolding`, `expectedShortfall`, `leadTimeLaw` and `newsvendorLevel`.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–10, §2 (1), (2), §2.1, Lemma 1, (4); p. ec1, the state space 𝒳

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

/-!
# Perishable lost-sales inventory under FIFO issuance (Bu, Gong & Chao, §2)

Time is zero-based: Lean period `t` is the paper's period `t + 1`, and the demand
`d t` of a path `d : CappedBaseStock.DemandPath` is the paper's `D_{t+1}`.

The state `x : Fin (m - 1) → ℝ` holds the *cumulative* levels: `x ⟨i - 1, _⟩` is the
paper's `x_{t,i}`, the stock whose remaining lifetime is at most `i` periods. The
paper's `x_{t,0}` is `0`, so for `m = 1` the state is empty and the order-up-to level
is the order itself. All costs and long-run averages take values in `ℝ≥0∞`, and
expectations are lower Lebesgue integrals over the i.i.d. demand path law.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

/-- The paper's standing parameters (p. 8): a lifetime `m ≥ 1`, a unit holding cost
`h > 0`, a unit lost-sales penalty `p > 0` and an additional unit outdating cost
`θ ≥ 0`. -/
structure Params where
  m : ℕ
  one_le_m : 1 ≤ m
  h : ℝ
  p : ℝ
  θ : ℝ
  h_pos : 0 < h
  p_pos : 0 < p
  θ_nonneg : 0 ≤ θ

/-- The system state `(x_{t,1}, …, x_{t,m-1})` of cumulative inventory levels. -/
abbrev State (m : ℕ) := Fin (m - 1) → ℝ

/-- The empty state `x_1 = 0` of p. 8. -/
def emptyState (m : ℕ) : State m := fun _ => 0

/-- `x_{t,m-1}`, with the convention `x_{t,0} = 0` when `m = 1`. -/
def topLevel {m : ℕ} (x : State m) : ℝ :=
  if h : 0 < m - 1 then x ⟨m - 2, by omega⟩ else 0

/-- The total inventory level after ordering, `x_{t,m} = x_{t,m-1} + q_t`. -/
def orderUpTo {m : ℕ} (x : State m) (q : ℝ≥0) : ℝ := topLevel x + q

/-- `x_{t,1}`; when `m = 1` this is `x_{t,m}`. -/
def firstLevel {m : ℕ} (x : State m) (q : ℝ≥0) : ℝ :=
  if h : 0 < m - 1 then x ⟨0, h⟩ else orderUpTo x q

/-- `x_{t,i+1}` for the index `j = i - 1` of `x_{t+1,i}`; for `i = m - 1` this is
`x_{t,m}`. -/
def levelAbove {m : ℕ} (x : State m) (q : ℝ≥0) (j : Fin (m - 1)) : ℝ :=
  if h : j.val + 1 < m - 1 then x ⟨j.val + 1, h⟩ else orderUpTo x q

/-- Outdated quantity `o_t = (x_{t,1} - D_t)^+` (p. 8). -/
def outdate {m : ℕ} (x : State m) (q d : ℝ≥0) : ℝ :=
  max (firstLevel x q - d) 0

/-- FIFO dynamics (1), p. 8: `x_{t+1,i} = (x_{t,i+1} - D_t - o_t)^+`. -/
def step {m : ℕ} (x : State m) (q d : ℝ≥0) : State m :=
  fun j => max (levelAbove x q j - d - outdate x q d) 0

/-- Admissible policies Π (p. 9): in each period `t` the order is a non-negative
measurable function `φ_t(x_t)` of the current state. -/
structure Policy (m : ℕ) where
  φ : ℕ → State m → ℝ≥0
  measurable_φ : ∀ t, Measurable (φ t)

/-- The trajectory of policy `π` from initial state `x₀` along demand path `d`.
The state in period `t` depends on `d 0, …, d (t - 1)` only. -/
def runFrom {m : ℕ} (x₀ : State m) (π : Policy m) (d : CappedBaseStock.DemandPath) :
    ℕ → State m
  | 0 => x₀
  | t + 1 => step (runFrom x₀ π d t) (π.φ t (runFrom x₀ π d t)) (d t)

/-- The trajectory from the empty initial state (p. 8). -/
def run {m : ℕ} (π : Policy m) (d : CappedBaseStock.DemandPath) : ℕ → State m :=
  runFrom (emptyState m) π d

/-- `x^π_{t,m}` from the empty state. -/
def upTo {m : ℕ} (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  orderUpTo (run π d t) (π.φ t (run π d t))

/-- `o^π_t` from initial state `x₀`. -/
def outdateFrom {m : ℕ} (x₀ : State m) (π : Policy m) (d : CappedBaseStock.DemandPath)
    (t : ℕ) : ℝ :=
  outdate (runFrom x₀ π d t) (π.φ t (runFrom x₀ π d t)) (d t)

/-- `o^π_t` from the empty state. -/
def outdated {m : ℕ} (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  outdateFrom (emptyState m) π d t

/-- Period cost (2): `h(x_{t,m} - D_t)^+ + p(D_t - x_{t,m})^+ + θ o_t`. -/
def periodCost (c : Params) (π : Policy c.m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (upTo π d t - d t) 0) +
    ENNReal.ofReal (c.p * max ((d t : ℝ) - upTo π d t) 0) +
    ENNReal.ofReal (c.θ * outdated π d t)

/-- `limsup_{T→∞} (1/T) Σ_{t=1}^T E[X_t]`, written with `T + 1` periods (an index
shift that leaves the limsup unchanged). -/
def cesaroLimsup (P : CappedBaseStock.DemandLaw)
    (X : ℕ → CappedBaseStock.DemandPath → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1), ∫⁻ d, X t d ∂CappedBaseStock.demandPathLaw P) /
      ((T : ℝ≥0∞) + 1)) atTop

/-- The long-run average cost `C^π` (p. 9). -/
def policyCost (P : CappedBaseStock.DemandLaw) (c : Params) (π : Policy c.m) : ℝ≥0∞ :=
  cesaroLimsup P (fun t d => periodCost c π d t)

/-- `OPT = inf_{π ∈ Π} C^π` over all admissible policies (p. 9). -/
def OPT (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ≥0∞ :=
  ⨅ π : Policy c.m, policyCost P c π

lemma measurable_topLevel (m : ℕ) : Measurable (fun x : State m => topLevel x) := by
  unfold topLevel
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The base-stock policy `π_S`: order `q_t = (S - x_{t,m-1})^+` (p. 9). -/
def baseStock (m : ℕ) (S : ℝ≥0) : Policy m where
  φ _ x := Real.toNNReal ((S : ℝ) - topLevel x)
  measurable_φ _ := Measurable.real_toNNReal (measurable_const.sub (measurable_topLevel m))

/-- `C(S)`: the long-run average cost of `π_S` from the empty state. -/
def bsCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost P c (baseStock c.m S)

/-- The state space `𝒳 = {0 ≤ x_1 ≤ ⋯ ≤ x_{m-1} ≤ S}` of `π_S` (ec1). -/
def BSStates (m : ℕ) (S : ℝ≥0) : Set (State m) :=
  {x | (∀ j, 0 ≤ x j) ∧ Monotone x ∧ ∀ j, x j ≤ S}

/-- Average expected outdating of `π_S` from initial state `x₀` over the first
`T + 1` periods. -/
def avgOutdateFrom (P : CappedBaseStock.DemandLaw) (m : ℕ) (S : ℝ≥0) (x₀ : State m)
    (T : ℕ) : ℝ≥0∞ :=
  (∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (outdateFrom x₀ (baseStock m S) d t)
      ∂CappedBaseStock.demandPathLaw P) / ((T : ℝ≥0∞) + 1)

/-- `ō(S)`, the long-run average expected outdating of `π_S` from the empty state:
the paper's `E[O_∞(S)]` (Lemma 1). -/
def avgOutdate (P : CappedBaseStock.DemandLaw) (m : ℕ) (S : ℝ≥0) : ℝ≥0∞ :=
  Filter.limsup (avgOutdateFrom P m S (emptyState m)) atTop

/-- The heuristic cost (4), p. 10:
`C̃(S) = hE[(S - D)^+] + pE[(D - S)^+] + (θ/m)E[(S - Σ_{i=1}^m D_i)^+]`. -/
def heuristicCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.p S +
    c.θ / c.m * LostSalesOrderUpTo.Asymptotic.expectedHolding
      (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S

/-- `S̃` is a minimizer of `C̃` over `[0, +∞)` (p. 10). -/
def IsHeuristicLevel (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, heuristicCost P c S ≤ heuristicCost P c S'

/-- `S^NP = F^{-1}(p/(p + h))` (p. 10). -/
def newsvendorNP (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ≥0 :=
  LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law c.h c.p

end PerishBaseStock.Lifetime


