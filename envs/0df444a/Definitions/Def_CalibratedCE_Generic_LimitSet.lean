-- Prove2me | Definitions.Def_CalibratedCE_Generic_LimitSet
-- name    : CalibratedCE_Generic_LimitSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:00:27.449089+00:00
-- url     : https://prove2.me/theorems/3efb1789-dbad-41e8-9a55-4c4345dc3214
-- title:
--   Limit points of calibrated forecasts and $\lambda(G)$ (Section 3, p. 46)
-- statement:
--   "DEFINITION. Call a point of the distribution $D(x,y)$ a *limit point of calibrated forecasts* if there exist deterministic best reply functions $R_i(\cdot)$ and calibrated forecasting rules $p_i$ such that if each player $i$, plays $R_i(p_i)$, then the limiting joint distribution will be $D(x,y)$." "DEFINITION. For a game $G$, let $\lambda(G)$ be the set of all distributions which are limit points of calibrated forecasts." (p. 46)
--
--   A **forecasting rule** is "a deterministic forecasting rule which depends only on observed histories" (p. 46): player 1's rule $\pi_1$ maps each finite history of play $((x_0,y_0),\dots,(x_{t-1},y_{t-1}))$ to a probability vector over $S(2)$, and player 2's rule $\pi_2$ maps it to a probability vector over $S(1)$. Given rules $\pi_1,\pi_2$ and best-reply functions $R_1,R_2$, the play is generated recursively: $h_0$ is the empty history, and in round $t$
--   $$f_1(t) = \pi_1(h_t),\quad f_2(t) = \pi_2(h_t),\quad x_t = R_1(f_1(t)),\quad y_t = R_2(f_2(t)),\quad h_{t+1} = h_t\,(x_t,y_t).$$
--   $\lambda(G)$ is the set of $D$ for which there exist best-reply functions $R_1,R_2$ and simplex-valued rules $\pi_1,\pi_2$ such that $f_1$ is calibrated with respect to $(y_t)$, $f_2$ is calibrated with respect to $(x_t)$, and
--   $$\lim_{t\to\infty} D_t(x,y) = D(x,y) \quad\text{for all } x \in S(1),\ y \in S(2).$$
--
--   The limit is a genuine limit, not an accumulation point: "Theorem 2 does not just find an accumulation point it finds a direct limit" (p. 48).
--
--   **Formalization Note** Since the length of the history is the round number, every forecast sequence along the realized play is produced by some rule, so rules and sequences give the same set. Rules are required to output probability vectors on every history. Best-reply functions are the stationary ones of p. 44; with round-dependent tie-breaking the set would be larger (the matching pennies example of p. 46).
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 46, Section 3, Definition (limit point of calibrated forecasts) and Definition (λ(G))

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration

namespace CalibratedCE.Generic

open Filter Topology

/-- The history of play generated when player `i` forecasts with the history-dependent rule `πᵢ`
and plays `Rᵢ` of that forecast: `hist 0 = []` and round `t` appends
`(R₁ (π₁ (hist t)), R₂ (π₂ (hist t)))`. -/
def hist {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ) :
    ℕ → List (Fin m × Fin n)
  | 0 => []
  | t + 1 =>
    let h := hist R₁ R₂ π₁ π₂ t
    h ++ [(R₁ (π₁ h), R₂ (π₂ h))]

/-- Player 1's forecast (of player 2) in round `t`. -/
def forecast₁ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin n → ℝ :=
  π₁ (hist R₁ R₂ π₁ π₂ t)

/-- Player 2's forecast (of player 1) in round `t`. -/
def forecast₂ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin m → ℝ :=
  π₂ (hist R₁ R₂ π₁ π₂ t)

/-- Player 1's play in round `t`: `R₁` of player 1's forecast. -/
def play₁ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin m :=
  R₁ (forecast₁ R₁ R₂ π₁ π₂ t)

/-- Player 2's play in round `t`: `R₂` of player 2's forecast. -/
def play₂ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin n :=
  R₂ (forecast₂ R₁ R₂ π₁ π₂ t)

/-- `λ(G)`: the joint distributions `D` that are limit points of calibrated forecasts. There are
stationary deterministic best-reply functions `R₁, R₂` and history-dependent forecasting rules
`π₁, π₂` with values in the simplex, such that each player's forecasts are calibrated against the
other player's plays and the empirical joint distribution of play converges to `D`. -/
def LimitSet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | ∃ (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
      (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ),
      IsBestReply₁ u₁ R₁ ∧ IsBestReply₂ u₂ R₂ ∧
      (∀ h, IsDist (π₁ h)) ∧ (∀ h, IsDist (π₂ h)) ∧
      Shared.Calibrated (forecast₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) ∧
      Shared.Calibrated (forecast₂ R₁ R₂ π₁ π₂) (play₁ R₁ R₂ π₁ π₂) ∧
      ∀ a b, Tendsto (fun t => empDist (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t a b)
        atTop (𝓝 (D a b))}

end CalibratedCE.Generic


