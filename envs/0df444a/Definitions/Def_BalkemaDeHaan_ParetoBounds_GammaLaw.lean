-- Prove2me | Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
-- name    : BalkemaDeHaan_ParetoBounds_GammaLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:22.494765+00:00
-- url     : https://prove2.me/theorems/b04f682a-88a9-4aea-9189-586a7ddc467a
-- title:
--   The Pareto-type limit law $\Gamma_\alpha(x) = 1 - (1 + x)^{-\alpha}$, $x \ge 0$
-- statement:
--   For a positive constant $\alpha$, the distribution function $\Gamma_\alpha$ is
--
--   $$
--   \Gamma_\alpha(x) = \begin{cases} 1 - (1 + x)^{-\alpha}, & x \ge 0, \\ 0, & x < 0. \end{cases}
--   $$
--
--   It is the law of $Y - 1$ for a Pareto variable $Y$ with tail $P\{Y > y\} = y^{-\alpha}$, $y \ge 1$. Balkema and de Haan show that $\Gamma_\alpha$ is one of the possible limit laws of the residual life time scaled by the age $t$; like all their limit laws, it vanishes for $x < 0$.
--
--   **Formalization Note** The power is `Real.rpow`; for $x \ge 0$ the base $1 + x$ is at least $1$, so no junk value of `rpow` is involved. The definition is stated for every real $\alpha$, and the theorems that use it assume $\alpha > 0$, as the paper does.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 793 (PDF p. 2), definition of Γ_α

import Mathlib

namespace BalkemaDeHaan.ParetoBounds

/-- The limit law `Γ_α` of Balkema–de Haan (1974), p. 793:
`Γ_α(x) = 1 - (1 + x)^{-α}` for `x ≥ 0`, and `Γ_α(x) = 0` for `x < 0`
("All limit distributions vanish for x < 0"). The parameter `α` is meant to be positive. -/
noncomputable def GammaLaw (α x : ℝ) : ℝ :=
  if 0 ≤ x then 1 - (1 + x) ^ (-α) else 0

end BalkemaDeHaan.ParetoBounds


