-- Prove2me | Definitions.Def_CalibratedCE_Generic_Forecasts
-- name    : CalibratedCE_Generic_Forecasts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:01:38.55097+00:00
-- url     : https://prove2.me/theorems/9c980bb3-33e9-47a9-938b-8ae6927471b0
-- title:
--   The conditional forecasts $p_{1,t}, p_{2,t}$ and the perturbed forecasts $p_i^{x'}$ (proof of Theorem 2, pp. 47–48)
-- statement:
--   Two constructions from the proof of Theorem 2.
--
--   1. **Conditional forecasts** (p. 47). For a joint distribution $D$ over $S(1)\times S(2)$, when player 1 plays $x_t$ it forecasts
--   $$p_{1,t}(\cdot) = \frac{D(x_t,\cdot)}{\sum_{y\in S(2)} D(x_t,y)},$$
--   and when player 2 plays $y_t$ it forecasts
--   $$p_{2,t}(\cdot) = \frac{D(\cdot,y_t)}{\sum_{x\in S(1)} D(x,y_t)}.$$
--   These are the conditional distributions of the opponent's strategy given one's own strategy under $D$. They depend on the round only through the strategy played.
--   2. **Perturbed forecasts** (p. 48). For vectors $p^*$ and $q$ over $S(2)$,
--   $$p_i = \left(1 - \tfrac{1}{i}\right)p^* + \tfrac{1}{i}\,q, \qquad i = 1,2,\dots$$
--
--   **Formalization Note** The page prints the denominator of $p_{2,t}$ as $\sum_{x\in S(1)} D(x_t, y)$, a typo for $\sum_{x \in S(1)} D(x, y_t)$ (the forecast must be a probability vector over $S(1)$); the corrected form is used. When the denominator is $0$ Lean's division gives the zero vector; the theorems using these forecasts assume positive denominators. $p_i$ is defined for every natural $i$ (at $i = 0$ it equals $p^*$, since $1/0 = 0$); the theorems use $i \ge 1$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, proof of Theorem (Theorem 2) (p_{1,t}, p_{2,t}); p. 48, proof of Theorem (Theorem 2) (p_i^{x′})

import Mathlib

namespace CalibratedCE.Generic

/-- Player 1's conditional forecast `p_{1,t}(·) = D(x_t, ·) / Σ_y D(x_t, y)` when player 1's
recommended strategy is `a`. -/
noncomputable def condForecast₁ {m n : ℕ} (D : Fin m → Fin n → ℝ) (a : Fin m) : Fin n → ℝ :=
  fun b => D a b / ∑ c, D a c

/-- Player 2's conditional forecast `p_{2,t}(·) = D(·, y_t) / Σ_x D(x, y_t)` when player 2's
recommended strategy is `b`. -/
noncomputable def condForecast₂ {m n : ℕ} (D : Fin m → Fin n → ℝ) (b : Fin n) : Fin m → ℝ :=
  fun a => D a b / ∑ c, D c b

/-- The perturbed forecasts `p_i = (1 - 1/i) p* + (1/i) q`, `i = 1, 2, …`. -/
noncomputable def pert {n : ℕ} (pstar q : Fin n → ℝ) (i : ℕ) : Fin n → ℝ :=
  fun b => (1 - 1 / (i : ℝ)) * pstar b + (1 / (i : ℝ)) * q b

end CalibratedCE.Generic


