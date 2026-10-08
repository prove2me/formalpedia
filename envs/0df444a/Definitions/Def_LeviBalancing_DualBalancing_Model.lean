-- Prove2me | Definitions.Def_LeviBalancing_DualBalancing_Model
-- name    : LeviBalancing_DualBalancing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:27.529125+00:00
-- url     : https://prove2.me/theorems/c3077c04-a0bb-4458-9a98-6b705c05a29e
-- title:
--   §2–§3.2, pp. 288–292 — the periodic-review inventory model with lead time $L$ and $c_t=0$: positions $X_t, Y_t$, net inventory, period costs, marginal costs $H_t$, $\Pi_t$ (Eqs. (1)–(4))
-- statement:
--   This file fixes the deterministic (one-realization) layer of the uncapacitated periodic-review stochastic inventory control problem of Levi, Pál, Roundy and Shmoys (2007), in the form used throughout their §4: ordering costs $c_t = 0$ and no discounting.
--
--   **Instance.** There are $T$ periods $t = 1, \dots, T$ and a known integer lead time $L \ge 0$: an order placed in period $t$ arrives in period $t + L$. Period $t$ has a per-unit holding cost $h_t \ge 0$ and a per-unit backlogging penalty $p_t \ge 0$. The initial data are the net inventory $ni_0 \in \mathbb R$ at time $0$ (negative means backorders) and the pipeline orders $q_j \ge 0$, $1 - L \le j \le 0$, which arrive in periods $1, \dots, L$.
--
--   **One realization.** Fix demands $d_1, \dots, d_T$ and orders $Q_1, \dots, Q_T$; write $Q_j = q_j$ for $j \le 0$ and use the convention $d_j = 0$ for $j \le 0$. Let $D_{[s,t]} = \sum_{j=s}^{t} d_j$.
--
--   1. **Inventory position before ordering:** $X_t = NI_{t-1} + \sum_{j=t-L}^{t-1} Q_j = ni_0 + \sum_{j=1-L}^{t-1} Q_j - D_{[1,t-1]}$.
--   2. **Inventory position after ordering:** $Y_t = X_t + Q_t$.
--   3. **Net inventory at the end of period $t$:** in period $t$ the order of period $t - L$ arrives and then the demand $d_t$ is served, so $NI_t = NI_{t-1} + Q_{t-L} - d_t = ni_0 + \sum_{j=1-L}^{t-L} Q_j - D_{[1,t]}$.
--   4. **Period cost:** $h_t\,NI_t^+ + p_t\,NI_t^-$, where $x^+ = \max(x,0)$ and $x^- = \max(-x, 0)$.
--   5. **Marginal holding cost (Eq. (1), $c_t = 0$):** the holding cost the $Q_t$ units ordered in period $t$ incur until the end of the horizon,
--   $$H_t = \sum_{j=t+L}^{T} h_j\,\bigl(Q_t - (D_{[t,j]} - X_t)^+\bigr)^+ .$$
--   6. **Marginal backlogging cost (Eq. (2)):** the penalty incurred in period $t + L$,
--   $$\Pi_t = p_{t+L}\,\bigl(D_{[t,t+L]} - (X_t + Q_t)\bigr)^+ .$$
--   7. **Holding cost of units ordered before period 1,** $H_{(-\infty,0]} = \sum_{j=1}^{T} h_j (ni_0 - D_{[1,j]})^+ + \sum_{t=1-L}^{0}\sum_{j=t+L}^{T} h_j \bigl(q_t - (D_{[t,j]} - x_t)^+\bigr)^+$ with $x_t = ni_0 + \sum_{i=1-L}^{t-1} q_i$.
--   8. **The cost of Eq. (4):**
--   $$\mathcal C = \sum_{t=1}^{T-L} \bigl(H_t + \Pi_t\bigr).$$
--
--   These objects carry the marginal cost accounting of §3.2: each unit ordered in period $t$ is charged, at the time of ordering, all the holding cost it will ever incur, and each period's order is charged the backlogging penalty of the period in which it arrives.
--
--   **Formalization Note** Periods are integers (`ℤ`); the policy's order sequence `Q : ℤ → ℝ` is read only at $t \ge 1$, and `order` substitutes the pipeline $q_t$ for $t \le 0$. The convention $D_j = 0$ for $j \le 0$ is built into `cumDemand`, which sums only indices $j \ge 1$. All sums use integer `Finset.Icc`/`Ico` ranges, so $\sum_{t=1}^{T-L}$ is empty when $T \le L$. The page's Eq. (2) prints $X_{t+L}$ and its restatement on p. 292 prints $p_t$; both are typos, and the definitions use $X_t$ and $p_{t+L}$ as the text ("backlogging cost incurred in period $t+L$", "$= p(D_{[t,t+L]} - Y_t^B)^+$") requires. Nonnegativity of $h_t, p_t$ ($1 \le t \le T$) and of $q_j$ ($1-L \le j \le 0$) is part of the `Instance` structure.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 288–292 (PDF pp. 5–9), §2 events (i)–(iv), §3.2 Eqs. (1)–(4), §4 preamble (c_t = 0)

import Mathlib

noncomputable section

namespace LeviBalancing.DualBalancing

open Finset

/-- An instance of the uncapacitated periodic-review stochastic inventory control problem of
Levi, Pál, Roundy & Shmoys (2007), §2, pp. 288–290, in the transformed form of §4 (p. 292):
ordering costs `c_t = 0` and no discounting (`α = 1`).

* `T` is the number of periods `1, …, T`; `L` is the (known, integer) lead time.
* `h t` is the per-unit holding cost and `p t` the per-unit backlogging penalty of period `t`;
  both are nonnegative for `t = 1, …, T`.
* `ni0` is the net inventory at time `0` (it may be negative, i.e. backorders).
* `q j`, for `1 - L ≤ j ≤ 0`, are the last `L` orders, placed before the horizon and arriving in
  periods `1, …, L`; they are nonnegative.

Periods are integers (`ℤ`); values of `h`, `p`, `q` outside the stated ranges are never used. -/
structure Instance where
  T : ℕ
  L : ℕ
  h : ℤ → ℝ
  p : ℤ → ℝ
  ni0 : ℝ
  q : ℤ → ℝ
  h_nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → 0 ≤ h t
  p_nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → 0 ≤ p t
  q_nonneg : ∀ j : ℤ, 1 - (L : ℤ) ≤ j → j ≤ 0 → 0 ≤ q j

/-- Accumulated demand `D_[s,t] = ∑_{j=s}^{t} d_j` along a demand path `d`, with the paper's
convention `D_j := 0` for `j ≤ 0` (p. 291): only indices `j ≥ 1` are summed. -/
def cumDemand (d : ℤ → ℝ) (s t : ℤ) : ℝ :=
  ∑ j ∈ Icc (max s 1) t, d j

/-- The order placed in period `t`: the given pipeline order `q_t` for `t ≤ 0`
(`Q_t^P = q_t` for `t ≤ 0`, p. 291) and the policy's order `Q t` for `t ≥ 1`. -/
def order (I : Instance) (Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  if t ≤ 0 then I.q t else Q t

/-- Inventory position `X_t` at the beginning of period `t`, before ordering (p. 289):
`X_t = NI_{t-1} + ∑_{j=t-L}^{t-1} Q_j`, which unrolls to
`X_t = ni_0 + ∑_{j=1-L}^{t-1} Q_j − D_[1,t−1]`. -/
def invPosition (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.ni0 + ∑ j ∈ Ico (1 - (I.L : ℤ)) t, order I Q j - cumDemand d 1 (t - 1)

/-- Inventory position after ordering in period `t`: `Y_t = X_t + Q_t` (p. 289). -/
def invPositionAfter (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  invPosition I d Q t + order I Q t

/-- Net inventory `NI_t` at the end of period `t` (p. 289, events (i)–(iii)): the order placed in
period `t − L` arrives in period `t`, then demand `d_t` is served, so
`NI_t = NI_{t−1} + Q_{t−L} − D_t = ni_0 + ∑_{j=1-L}^{t-L} Q_j − D_[1,t]`. -/
def netInventory (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.ni0 + ∑ j ∈ Icc (1 - (I.L : ℤ)) (t - I.L), order I Q j - cumDemand d 1 t

/-- The (traditional) cost of period `t` (p. 289, event (iv), with `c_t = 0`): holding cost
`h_t · NI_t⁺` plus backlogging penalty `p_t · NI_t⁻`. -/
def periodCost (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.h t * max (netInventory I d Q t) 0 + I.p t * max (-netInventory I d Q t) 0

/-- Marginal holding cost, Eq. (1) with `c_t = 0` (pp. 291–292):
`H_t = ∑_{j=t+L}^{T} h_j (Q_t − (D_[t,j] − X_t)⁺)⁺`, the holding cost the `Q_t` units ordered in
period `t` incur from their arrival until the end of the horizon. -/
def marginalHolding (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑ j ∈ Icc (t + I.L) (I.T : ℤ),
    I.h j * max (order I Q t - max (cumDemand d t j - invPosition I d Q t) 0) 0

/-- Marginal backlogging cost, Eq. (2) (p. 291): the backlogging penalty incurred in period
`t + L`, `Π_t = p_{t+L} (D_[t,t+L] − (X_t + Q_t))⁺ = p_{t+L} (D_[t,t+L] − Y_t)⁺`. -/
def marginalBacklog (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.p (t + I.L) * max (cumDemand d t (t + I.L) - invPositionAfter I d Q t) 0

/-- `H_(−∞,0]` of Eq. (3) (p. 291): the total holding cost incurred over periods `1, …, T` by
units ordered before period 1, i.e. by the initial on-hand stock `ni_0⁺` and by the pipeline
orders `q_t`, `1 − L ≤ t ≤ 0` (each held from its arrival period `t + L` on, by the
first-ordered, first-consumed rule of §3.2). It depends only on the instance and the demand
path. -/
def initialHolding (I : Instance) (d : ℤ → ℝ) : ℝ :=
  ∑ j ∈ Icc (1 : ℤ) (I.T : ℤ), I.h j * max (I.ni0 - cumDemand d 1 j) 0 +
  ∑ t ∈ Icc (1 - (I.L : ℤ)) 0, ∑ j ∈ Icc (t + I.L) (I.T : ℤ),
    I.h j * max (I.q t -
      max (cumDemand d t j - (I.ni0 + ∑ i ∈ Ico (1 - (I.L : ℤ)) t, I.q i)) 0) 0

/-- The cost `𝒞(P)` of Eq. (4) (p. 292) along one realization:
`𝒞(P) = ∑_{t=1}^{T−L} (H_t + Π_t)`. -/
def marginalCost (I : Instance) (d Q : ℤ → ℝ) : ℝ :=
  ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), (marginalHolding I d Q t + marginalBacklog I d Q t)

end LeviBalancing.DualBalancing

end


