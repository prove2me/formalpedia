-- Prove2me | Definitions.Def_CalibratedCE_Forecast_FracCalib
-- name    : CalibratedCE_Forecast_FracCalib
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:36:05.451976+00:00
-- url     : https://prove2.me/theorems/01a4f9dc-cd49-4d41-b6b5-395c320f6737
-- title:
--   Squared loss and fractional L-2 calibration of a grid forecaster (Appendix)
-- statement:
--   In the Appendix (pp. 53–54) player 1 forecasts from a finite grid of probability vectors $p^1,\dots,p^k\in\mathbb R^n$, choosing $p^i$ in round $t$ with probability $w_t^i$. Player 2's move in round $t$ is encoded by the 0–1 vector $X_t$ with $X_{t,j} = 1$ exactly when strategy $j$ was chosen. The loss of forecasting $p^i$ is
--
--   $$
--   L_t^i = |X_t - p^i|^2 = \sum_j (X_{t,j} - p^i_j)^2 .
--   $$
--
--   With $N_w(i,T) = \sum_{t=1}^{T} w_t^i$ the expected number of uses of $p^i$, and
--   $\rho_w(i,j,T) = \sum_{t=1}^{T} w_t^i X_{t,j} / N_w(i,T)$ (set to $0$ if $N_w(i,T)=0$) the weighted frequency of $j$ when $p^i$ is used, the **fractional L-2 calibration score** is
--
--   $$
--   C_{2,w}(T) = \sum_{i=1}^{k}\sum_{j} \bigl(\rho_w(i,j,T) - p^i_j\bigr)^2\,\frac{N_w(i,T)}{T}.
--   $$
--
--   It is the L-2 calibration score $C_2$ of p. 54, summed over $j$, with the indicator "forecast $p^i$ was issued in round $t$" replaced by its probability $w_t^i$. It is the quantity the Appendix compares with the regrets.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$. At $T = 0$ the division by $0$ gives $C_{2,w}(0) = 0$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), pp. 53–54, Appendix (grid p^i, X_t, loss L_t^i = |X_t − p^i|^2, C_2(t))

import Mathlib

namespace CalibratedCE.Forecast

/-- `X_{t,j}`: `1` if player 2 played strategy `j` in round `t`, `0` otherwise. -/
def ind {n : ℕ} (X : ℕ → Fin n) (t : ℕ) (j : Fin n) : ℝ :=
  if X t = j then 1 else 0

/-- The loss of forecasting the grid point `p^i` in round `t`:
`L_t^i = |X_t - p^i|^2 = ∑_j (X_{t,j} - p^i_j)^2`. -/
def sqLoss {k n : ℕ} (p : Fin k → Fin n → ℝ) (X : ℕ → Fin n) (t : ℕ) (i : Fin k) : ℝ :=
  ∑ j : Fin n, (ind X t j - p i j) ^ 2

/-- The expected number of times grid point `i` is forecast in rounds `0, …, T - 1` when it is
chosen with probability `w t i` in round `t`. -/
def Nw {k : ℕ} (w : ℕ → Fin k → ℝ) (T : ℕ) (i : Fin k) : ℝ :=
  ∑ t ∈ Finset.range T, w t i

/-- The `w`-weighted frequency of strategy `j` among the rounds in which grid point `i` is
forecast; `0` when `Nw w T i = 0`. -/
noncomputable def rhoW {k n : ℕ} (w : ℕ → Fin k → ℝ) (X : ℕ → Fin n) (T : ℕ) (i : Fin k)
    (j : Fin n) : ℝ :=
  if Nw w T i = 0 then 0
  else (∑ t ∈ Finset.range T, w t i * ind X t j) / Nw w T i

/-- The fractional L-2 calibration score after `T` rounds:
`∑_i ∑_j (ρ_w(i, j, T) - p^i_j)^2 N_w(i, T) / T`. -/
noncomputable def C2w {k n : ℕ} (p : Fin k → Fin n → ℝ) (w : ℕ → Fin k → ℝ) (X : ℕ → Fin n)
    (T : ℕ) : ℝ :=
  ∑ i : Fin k, ∑ j : Fin n, (rhoW w X T i j - p i j) ^ 2 * Nw w T i / (T : ℝ)

end CalibratedCE.Forecast


