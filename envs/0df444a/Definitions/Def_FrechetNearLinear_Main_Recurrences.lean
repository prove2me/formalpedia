-- Prove2me | Definitions.Def_FrechetNearLinear_Main_Recurrences
-- name    : FrechetNearLinear_Main_Recurrences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:10.488928+00:00
-- url     : https://prove2.me/theorems/dc95cff7-a2b4-4d6a-820e-f7a52894c3c5
-- title:
--   The query-exponent recurrence (5.1) and the parameter recurrence (7.1)
-- statement:
--   **(5.1).** For $\delta\in\mathbb R$ and $D\in\mathbb R$:
--   $$\beta_0=1,\quad \beta_{t+1}=\frac{\beta_t(1+\delta)}{1+\beta_t},\qquad A_0=1,\quad A_{t+1}=D(A_t+1)+A_t$$
--   (`queryExp δ t`, `queryFactor D t`).
--
--   **(7.1).** For $\varepsilon>0$ let $\bar\varepsilon=\min\{\varepsilon,1\}$, $K=\lceil 6/\bar\varepsilon\rceil$, $\theta=1/K$ and $T=\lceil(4/\theta)\log(16/\theta)\rceil$ with the natural logarithm. Set $(\alpha_0,\delta_0;D_0)=(1,0;9)$ and for $i\ge1$
--   $$\alpha_i=\frac{\alpha_{i-1}}{1+\alpha_{i-1}-\theta},\quad \delta_i=\frac{\theta}{1+\alpha_{i-1}-\theta},\quad D_i=2(D_{i-1}+1)^T+11$$
--   (`epsBar`, `numRounds`, `theta`, `innerDepth`, `roundAlpha`, `roundDelta`, `roundD`).
--
--   **Formalization Note** The paper uses (7.1) for $1\le i\le K$; the Lean sequences are defined for every $i$. `⌈·⌉₊` is the natural-number ceiling; its arguments are positive here.
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 23, (5.1); p. 33, Lemma 7.1, (7.1)

import Mathlib

/-!
# The recurrences (5.1) and (7.1)

Huang, Wang, Zhang, *Constant Approximation of Fréchet Distance in Near-Linear Time*, STOC 2027
submission (manuscript sha256 08be7e65…dd2d), p. 23 (5.1) and p. 33 (7.1), Lemma 7.1.

(5.1): `β₀ = 1`, `β_{t+1} = β_t (1 + δ) / (1 + β_t)`, `A₀ = 1`, `A_{t+1} = D (A_t + 1) + A_t`.

(7.1): for `ε > 0`, `ε̄ = min{ε, 1}`, `K = ⌈6 / ε̄⌉`, `θ = 1 / K`, `T = ⌈(4 / θ) log(16 / θ)⌉`
(natural logarithm), `(α₀, δ₀; D₀) = (1, 0; 9)`, `αᵢ = α_{i-1} / (1 + α_{i-1} - θ)`,
`δᵢ = θ / (1 + α_{i-1} - θ)`, `Dᵢ = 2 (D_{i-1} + 1)^T + 11`.
-/

namespace FrechetNearLinear.Main

/-- The query exponents `β_t` of (5.1) for self-query excess `δ`. -/
noncomputable def queryExp (δ : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => queryExp δ t * (1 + δ) / (1 + queryExp δ t)

/-- The approximation factors `A_t` of (5.1) for index factor `D`. -/
noncomputable def queryFactor (D : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => D * (queryFactor D t + 1) + queryFactor D t

/-- `ε̄ = min{ε, 1}`. -/
noncomputable def epsBar (ε : ℝ) : ℝ := min ε 1

/-- `K = ⌈6 / ε̄⌉`, the number of outer rounds. -/
noncomputable def numRounds (ε : ℝ) : ℕ := ⌈6 / epsBar ε⌉₊

/-- `θ = 1 / K`. -/
noncomputable def theta (ε : ℝ) : ℝ := 1 / (numRounds ε : ℝ)

/-- `T = ⌈(4 / θ) log(16 / θ)⌉`, the common inner depth (natural logarithm). -/
noncomputable def innerDepth (ε : ℝ) : ℕ := ⌈(4 / theta ε) * Real.log (16 / theta ε)⌉₊

/-- `αᵢ` of (7.1): `α₀ = 1`, `αᵢ = α_{i-1} / (1 + α_{i-1} - θ)`. -/
noncomputable def roundAlpha (ε : ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => roundAlpha ε i / (1 + roundAlpha ε i - theta ε)

/-- `δᵢ` of (7.1): `δ₀ = 0`, `δᵢ = θ / (1 + α_{i-1} - θ)`. -/
noncomputable def roundDelta (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => theta ε / (1 + roundAlpha ε i - theta ε)

/-- `Dᵢ` of (7.1): `D₀ = 9`, `Dᵢ = 2 (D_{i-1} + 1)^T + 11`. -/
noncomputable def roundD (ε : ℝ) : ℕ → ℝ
  | 0 => 9
  | i + 1 => 2 * (roundD ε i + 1) ^ innerDepth ε + 11

end FrechetNearLinear.Main


