-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Policy
-- name    : LeviBalancing_TripleBalancing_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:43:10.206348+00:00
-- url     : https://prove2.me/theorems/ec668a19-2554-43d9-b0b5-390e87b3898b
-- title:
--   §2 — feasible policies, inventory dynamics and the cost $\mathcal C(P)$ of the lot-sizing problem
-- statement:
--   Fix a stochastic lot-sizing model with periods $t=1,\dots,T$, information $\mathcal F_t$ at the beginning of period $t$, fixed ordering cost $K$, holding costs $h_t$, backlogging penalties $p_t$, initial inventory level $x_1$ and demands $D_t$.
--
--   A **feasible policy** is an order process $Q=(Q_t)_t$ with $Q_t\ge0$ and $Q_t$ measurable with respect to $\mathcal F_t$: the order of period $t$ uses only the information available at the beginning of period $t$ (which determines the current inventory level).
--
--   Under $Q$, with lead time zero, the inventory level at the beginning of period $t$ and the level after ordering are
--   $$x_t=x_1+\sum_{j=1}^{t-1}(Q_j-D_j),\qquad y_t=x_t+Q_t,$$
--   so $x_{t+1}=y_t-D_t$; negative levels are backorders. The cost of period $t$ is
--   $$K\,\mathbb 1(Q_t>0)+h_t\,(y_t-D_t)^+ + p_t\,(D_t-y_t)^+,$$
--   holding and backlogging being charged on the net inventory at the end of the period. The total cost is $\mathcal C(Q)=\sum_{t=1}^T(\text{cost of period }t)$, and the expected cost is $E[\mathcal C(Q)]\in[0,\infty]$.
--
--   These are the objects on which the comparison of the triple-balancing policy with every feasible policy is stated.
--
--   **Formalization Note** $E[\mathcal C(Q)]$ is the lower Lebesgue integral of the nonnegative total cost in $[0,\infty]$, so an infinite expected cost is $\infty$ and never collapses to $0$.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 289 (PDF 6), §2 (i)–(iv); p. 299 (PDF 16), §6 preamble

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model

open MeasureTheory

noncomputable section

namespace LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A feasible (nonanticipatory) policy is an order process `Q`, `Q t ω` the number of units
ordered in period `t`, with `Q t ≥ 0` and `Q t` determined by the information `ℱ t` available at
the beginning of period `t` (p. 289).  The current inventory level is itself `ℱ t`-measurable, so
this is the paper's "uses only `f_s` and the current inventory level". -/
def IsFeasiblePolicy (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 ≤ Q t ω) ∧ ∀ t, Measurable[M.ℱ t] (Q t)

/-- `x_t`: the inventory level at the beginning of period `t`, before ordering
(`x_1 = x₁`, `x_{t+1} = x_t + Q_t − D_t`; lead time `L = 0`). -/
def levelBefore (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.x₁ + ∑ j ∈ Finset.Ico 1 t, (Q j ω - M.D j ω)

/-- `y_t = x_t + Q_t`: the inventory level after the order of period `t`. -/
def levelAfter (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  levelBefore M Q t ω + Q t ω

/-- Cost of period `t`: the fixed cost `K` if `Q_t > 0`, the holding cost `h_t (y_t − D_t)⁺` and the
backlogging penalty `p_t (D_t − y_t)⁺` charged on the net inventory at the end of period `t`
(p. 289 (iv), p. 299). -/
def periodCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (if 0 < Q t ω then M.K else 0)
    + M.h t * max (levelAfter M Q t ω - M.D t ω) 0
    + M.p t * max (M.D t ω - levelAfter M Q t ω) 0

/-- `𝒞(Q)`: the total cost over periods `1, …, T` (undiscounted, `α = 1`). -/
def totalCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 M.T, periodCost M Q t ω

/-- `E[𝒞(Q)]`, as the lower Lebesgue integral of the nonnegative total cost in `ℝ≥0∞`
(an infinite expected cost is `⊤`, never `0`). -/
def expectedCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (totalCost M Q ω) ∂M.μ

end LeviBalancing.TripleBalancing

end


