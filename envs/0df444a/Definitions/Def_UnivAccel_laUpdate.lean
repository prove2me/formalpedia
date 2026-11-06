-- Prove2me | Definitions.Def_UnivAccel_laUpdate
-- name    : UnivAccel_laUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:05.53012+00:00
-- url     : https://prove2.me/theorems/9c34bddb-27ee-4778-af24-3f595662cbc7
-- title:
--   Lookahead update (44) and the duration (43)
-- statement:
--   Fix $\mu > 0$, a radius $r > 0$ and a duration $h > 0$. From the state $(\bar x, \bar w)$ the lookahead method predicts
--   $$
--   x_p = \frac{\bar x + h \bar w}{1 + h\sqrt\mu},
--   $$
--   queries the ball oracle at $x_p$ for $x_c$ and reads $g = \nabla f(x_c)$; with
--   $$
--   \eta = \frac{r}{\|g\| + \mu r}, \qquad \alpha = \min\{1, \eta/h^2\},
--   $$
--   it updates
--   $$
--   \bar x_+ = (1 - \alpha)\bar x + \alpha x_c, \qquad \bar w_+ = (1 - \alpha h\sqrt\mu)\bar w + \alpha h(\mu x_c - g). \tag{44}
--   $$
--   The module defines the predicted point (`laPredict`), $\eta$ (`laEta`), $\alpha$ (`laAlpha`), the update (`laUpdate`, given $x_c$ and $g$) and the duration of (43),
--   $$
--   h = \frac{1}{\sqrt\mu}\min\Big\{\frac12, \Big(\frac{\mu r^2}{\mathcal H}\Big)^{1/3}\Big\} \qquad (`laStepSize`),
--   $$
--   for a known upper bound $\mathcal H > 0$ on the potential.
--
--   **Formalization Note** The oracle call is made by the caller (`laPhaseStep`); $(\cdot)^{1/3}$ is `Real.rpow`.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.3, eqs. (40), (43), (44), p.23

import Mathlib

namespace UnivAccel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The predicted point of the lookahead method (44), `x_p = (x̄ + h w̄)/(1 + h√μ)`
(Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027
submission manuscript (sha256 c7b64bc2…980250), eq. (44), p.23). -/
noncomputable def laPredict (μ h : ℝ) (x w : E) : E :=
  (1 + h * Real.sqrt μ)⁻¹ • (x + h • w)

/-- The ball step length `η = r/(‖g‖ + μr)` of (44), where `g = ∇f(x_c)` (same source, p.23). -/
noncomputable def laEta (μ r : ℝ) (g : E) : ℝ :=
  r / (‖g‖ + μ * r)

/-- The step fraction `α = min{1, η/h²}` of (40) and (44) (same source, p.23). -/
noncomputable def laAlpha (μ r h : ℝ) (g : E) : ℝ :=
  min 1 (laEta μ r g / h ^ 2)

/-- The duration (43), `h = (1/√μ) min{1/2, (μr²/𝓗)^{1/3}}`, for an upper bound `𝓗` on the
potential (same source, p.23).

**Formalization Note** `(·)^{1/3}` is `Real.rpow`; the argument is positive whenever
`μ, r, 𝓗 > 0`. -/
noncomputable def laStepSize (μ r Hbar : ℝ) : ℝ :=
  (Real.sqrt μ)⁻¹ * min (1 / 2) ((μ * r ^ 2 / Hbar) ^ ((1 : ℝ) / 3))

/-- One update of the lookahead method (44) (Adil–Kyng, *Universal Acceleration: New Approaches
to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), p.23):
from the state `(x̄, w̄)`, the duration `h`, the ball-oracle answer `x_c` at the predicted point
and the gradient `g = ∇f(x_c)` there, with `α = min{1, η/h²}`, `η = r/(‖g‖ + μr)`,
`x̄₊ = (1 − α)x̄ + α x_c`,  `w̄₊ = (1 − αh√μ) w̄ + αh (μ x_c − g)`.

**Formalization Note** The oracle call itself is made by the caller; this function only applies
the update of (44) to its answer. -/
noncomputable def laUpdate (μ r h : ℝ) (x w xc g : E) : E × E :=
  let α := laAlpha μ r h g
  ((1 - α) • x + α • xc, (1 - α * h * Real.sqrt μ) • w + (α * h) • (μ • xc - g))

end UnivAccel


