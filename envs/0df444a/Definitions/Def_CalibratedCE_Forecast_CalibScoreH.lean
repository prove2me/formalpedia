-- Prove2me | Definitions.Def_CalibratedCE_Forecast_CalibScoreH
-- name    : CalibratedCE_Forecast_CalibScoreH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:35:03.705143+00:00
-- url     : https://prove2.me/theorems/a5dca10e-f491-496b-9be1-4de56bcb31cb
-- title:
--   Calibration scores $N(p,t)$, $\rho(p,j,t)$, $C_t$ and $C_2(t)$ of a finite history
-- statement:
--   Player 1 forecasts the play of player 2, who has $n$ pure strategies $j\in\{0,\dots,n-1\}$. A **history** of length $t$ is the list $h = ((p_1,j_1),\dots,(p_t,j_t))$ of the forecasts $p_s\in\mathbb R^n$ issued by player 1 and the strategies $j_s$ played by player 2 in rounds $1,\dots,t$. Following Foster and Vohra (pp. 43–44):
--
--   1. $N(p,t)$ is the number of rounds $s\le t$ with $p_s = p$;
--   2. $\rho(p,j,t)$ is, among those rounds, the fraction in which player 2 played $j$; it is set to $0$ when $N(p,t)=0$;
--   3. the **calibration score** of Eq. (1) (p. 49) is
--   $$
--   C_t \;=\; \sum_{p}\ \sum_{j} \bigl|\rho(p,j,t) - p_j\bigr|\,\frac{N(p,t)}{t},
--   $$
--   4. for a single strategy $j$ the **L-1** and **L-2 calibration scores** (p. 54) are
--   $$
--   C^{(j)}(t) = \sum_p \bigl|\rho(p,j,t) - p_j\bigr|\frac{N(p,t)}{t}, \qquad
--   C_2^{(j)}(t) = \sum_p \bigl(\rho(p,j,t) - p_j\bigr)^2\frac{N(p,t)}{t}.
--   $$
--
--   The sums over $p$ run over the forecasts that actually occur in $h$; every other $p$ has $N(p,t)=0$ and contributes nothing, as the paper notes ("it would be multiplied by zero anyway", p. 44). A forecast sequence is calibrated when these scores tend to zero.
--
--   **Formalization Note** Forecasts are compared by exact equality of vectors in $\mathbb R^n$ (classical decidability). The history is a Lean list, oldest round first; $t$ is its length. For the empty history the division by $t = 0$ gives $0$, so every score of the empty history is $0$. $C_t$ is the per-$j$ calibration score of the paper's Section 2 summed over $j$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), pp. 43–44, Section 2 (N(p, t), ρ(p, j, t), calibration); p. 49, Eq. (1); p. 54, Appendix (C_2(t))

import Mathlib

namespace CalibratedCE.Forecast

open Classical

/-- `N(p, t)` read off a finite history `h` of (forecast, opponent's play) pairs, oldest first:
the number of rounds of `h` in which the forecast was exactly the vector `p`. -/
noncomputable def NH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) : ℕ :=
  (h.filter (fun e => e.1 = p)).length

/-- `ρ(p, j, t)` read off a history `h`: among the rounds of `h` with forecast `p`, the fraction
in which the opponent played `j`; it is `0` when `p` was never forecast. -/
noncomputable def rhoH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    ℝ :=
  if NH h p = 0 then 0
  else ((h.filter (fun e => e.1 = p ∧ e.2 = j)).length : ℝ) / (NH h p : ℝ)

/-- The calibration score `C_t` of Eq. (1), read off a history `h` of length `t`:
`∑_p ∑_j |ρ(p, j, t) - p_j| N(p, t) / t`, the sum over `p` running over the forecasts that occur
in `h` (every other `p` has `N(p, t) = 0`). -/
noncomputable def calibScoreH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, ∑ j : Fin n,
    |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ)

/-- The L-1 calibration score for the single opponent strategy `j`:
`∑_p |ρ(p, j, t) - p_j| N(p, t) / t`. -/
noncomputable def calibScoreHj {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ)

/-- The L-2 calibration score `C_2(t)` for the opponent strategy `j` (p. 54):
`∑_p (ρ(p, j, t) - p_j)^2 N(p, t) / t`. -/
noncomputable def calibScore2Hj {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, (rhoH h p j - p j) ^ 2 * (NH h p : ℝ) / (h.length : ℝ)

end CalibratedCE.Forecast


