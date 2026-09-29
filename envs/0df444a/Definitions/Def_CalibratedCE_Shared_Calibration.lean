-- Prove2me | Definitions.Def_CalibratedCE_Shared_Calibration
-- name    : CalibratedCE_Shared_Calibration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:26:42.036955+00:00
-- url     : https://prove2.me/theorems/5542d368-a52d-4956-8ba7-9855be434e7a
-- title:
--   Calibrated forecasts: $N(p,t)$, $\rho(p,j,t)$ and the calibration score (Section 2, pp. 43–44)
-- statement:
--   A forecaster predicts, in every round $s$, the opponent's play by a vector $f(s) = (f_1(s), \dots, f_k(s))$, where $k$ is the number of the opponent's strategies and $f_j(s)$ is "the forecasted probability that player 2 will play strategy $j$" (p. 43). The opponent's plays are $z(s) \in \{0, \dots, k-1\}$, and $\chi(j, s) = 1$ if $z(s) = j$ and $0$ otherwise.
--
--   The paper (p. 43): "Denote by $N(p, t)$ the number of rounds up to the $t$-th round that $f$ generated a vector of forecasts equal to $p$. Let $\rho(p, j, t)$ be the fraction of these rounds for which player 2 plays $j$", i.e.
--   $$\rho(p, j, t) = \begin{cases} 0 & \text{if } N(p, t) = 0, \\ \displaystyle\sum_{s=1}^{t} \frac{I_{f(s) = p}\, \chi(j, s)}{N(p, t)} & \text{otherwise.} \end{cases}$$
--   The **calibration score** of $f$ at strategy $j$ and time $t$ is
--   $$C_j(t) = \sum_{p} |\rho(p, j, t) - p_j| \frac{N(p, t)}{t},$$
--   and (p. 44) "The forecast $f$ is said to be calibrated with respect to the sequences of plays made by player 2 if
--   $$\lim_{t \to \infty} \sum_p |\rho(p, j, t) - p_j| \frac{N(p, t)}{t} = 0$$
--   for all $j \in S(2)$."
--
--   Calibration is the hypothesis of Theorem 1: each player's forecast of the other must be calibrated against the other's actual plays.
--
--   It serves chunk 01-calibration-implies-ce (pp. 43–44, Section 2; the hypothesis of Theorem 1, p. 44, and the calibration steps of its proof, pp. 44–45; the matching pennies example, p. 46) and chunk 02-generic-converse (pp. 43–44, Section 2; the definition of limit points of calibrated forecasts and $\lambda(G)$, p. 46; Theorem 1 restated as $\lambda(G) \subseteq \pi(G)$, p. 46; the calibrated conditional forecasts of the proof of Theorem 2, p. 47; the example after Theorem 2, p. 48).
--
--   **Formalization Note** Rounds are indexed from $0$: "the first $t$ rounds" are $s = 0, \dots, t-1$ (the paper's $s = 1, \dots, t$). The paper's $\sum_p$ runs over all vectors $p$; only the finitely many forecasts issued in the first $t$ rounds have $N(p, t) \neq 0$, and the paper notes that the other terms are multiplied by zero, so the sum is taken over the issued forecasts. The case $N(p,t) = 0$ of $\rho$ is kept as on the page. The definitions are stated for an opponent with $k$ strategies, so player 1 uses $k = n$ and player 2 uses $k = m$. Forecasts are compared for exact equality (real vectors). At $t = 0$ the score is $0$ by Lean's convention $x/0 = 0$; only the limit matters.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 43, Section 2 (N(p, t), ρ(p, j, t)); p. 44, Section 2 (definition of calibrated)

import Mathlib

open Filter Topology

namespace CalibratedCE.Shared

/-- `N(p, t)`: the number of rounds among the first `t` (rounds `0, …, t-1`) in which the
forecast sequence `f` issued the forecast vector `p`. -/
noncomputable def N {k : ℕ} (f : ℕ → Fin k → ℝ) (p : Fin k → ℝ) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => f s = p)).card

/-- `ρ(p, j, t)`: among the first `t` rounds in which `f` forecast `p`, the fraction in which
the opponent played `j`; it is `0` when `N(p, t) = 0`. -/
noncomputable def rho {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (p : Fin k → ℝ) (j : Fin k)
    (t : ℕ) : ℝ :=
  if N f p t = 0 then 0
  else (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) / (N f p t : ℝ)

/-- The calibration score `∑_p |ρ(p, j, t) - p_j| N(p, t) / t`, the sum running over the
forecasts issued in the first `t` rounds (every other `p` has `N(p, t) = 0`). -/
noncomputable def calibScore {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (j : Fin k)
    (t : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range t).image f, |rho f z p j t - p j| * (N f p t : ℝ) / (t : ℝ)

/-- The forecast sequence `f` is calibrated with respect to the opponent's plays `z`: for every
opponent strategy `j` the calibration score tends to `0`. -/
def Calibrated {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) : Prop :=
  ∀ j : Fin k, Tendsto (fun t : ℕ => calibScore f z j t) atTop (𝓝 0)

end CalibratedCE.Shared


