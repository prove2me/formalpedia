-- Prove2me | Definitions.Def_LorentzFactorDefs
-- name    : LorentzFactorDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T19:29:48.673519+00:00
-- url     : https://prove2.me/theorems/b5302bd5-c049-44cc-b85a-79854fd16f38
-- title:
--   Lorentz factor $\gamma$, its reciprocal, velocity addition, and the boost matrix
-- statement:
--   Working in units where the speed of light is $c = 1$, so that the only kinematic parameter is $\beta = v/c$, this file fixes the four objects the mission is about.
--
--   - $\gamma(\beta) = \dfrac{1}{\sqrt{1 - \beta^{2}}}$, the **Lorentz factor**.
--   - $\alpha(\beta) = \sqrt{1 - \beta^{2}}$, its **reciprocal**, the quantity denoted $1/\gamma$ in the source article.
--   - $\beta_1 \oplus \beta_2 = \dfrac{\beta_1 + \beta_2}{1 + \beta_1\beta_2}$, **relativistic velocity addition**.
--   - $B(\beta) = \begin{pmatrix} \gamma(\beta) & -\gamma(\beta)\beta \\ -\gamma(\beta)\beta & \gamma(\beta)\end{pmatrix}$, the **Lorentz boost** along the $x$-axis acting on the coordinate pair $(t, x)$, i.e. $t' = \gamma(t - \beta x)$, $x' = \gamma(x - \beta t)$.
--
--   The definitions are total functions of a real argument. For $|\beta| \ge 1$ the radicand $1 - \beta^{2}$ is non-positive, the real square root returns $0$, and $\gamma(\beta) = 1/0 = 0$; every statement in the mission that needs the physical regime carries an explicit hypothesis $|\beta| < 1$. Likewise $\beta_1 \oplus \beta_2$ evaluates to $0$ when $1 + \beta_1\beta_2 = 0$, which cannot happen when both velocities are subluminal.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib

namespace LorentzFactor

/-- The Lorentz factor `gamma β = 1 / √(1 - β ^ 2)`, in units where the speed of light
is `c = 1`, so that `β = v / c` is the relative velocity.  For `|β| ≥ 1` the square root
is the junk value `0` and `gamma β = 0`. -/
noncomputable def gamma (β : ℝ) : ℝ := 1 / Real.sqrt (1 - β ^ 2)

/-- The reciprocal Lorentz factor `alpha β = √(1 - β ^ 2)`. -/
noncomputable def alpha (β : ℝ) : ℝ := Real.sqrt (1 - β ^ 2)

/-- Relativistic velocity addition, `velAdd β₁ β₂ = (β₁ + β₂) / (1 + β₁ * β₂)`, in units
where `c = 1`. -/
noncomputable def velAdd (β₁ β₂ : ℝ) : ℝ := (β₁ + β₂) / (1 + β₁ * β₂)

/-- The Lorentz boost of velocity `β` along the `x`-axis, as a `2 × 2` matrix acting on
the coordinate pair `(t, x)` with `c = 1`:
`t' = gamma β * (t - β * x)` and `x' = gamma β * (x - β * t)`. -/
noncomputable def boost (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gamma β, -(gamma β * β); -(gamma β * β), gamma β]

end LorentzFactor


