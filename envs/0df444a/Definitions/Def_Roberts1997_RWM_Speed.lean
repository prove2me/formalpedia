-- Prove2me | Definitions.Def_Roberts1997_RWM_Speed
-- name    : Roberts1997_RWM_Speed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:43:55.06482+00:00
-- url     : https://prove2.me/theorems/eb1fe7ea-fc6b-4ebe-ada9-9e4f7ddae0ea
-- title:
--   Roughness I, standard normal cdf Φ, speed h(l) = 2l²Φ(−l√I/2) and limiting acceptance rate a(l) = 2Φ(−l√I/2)
-- statement:
--   Let $\Phi$ be the standard normal cumulative distribution function. For a density $f$ the paper (p. 112) sets
--
--   $$ I = \mathbb E_f\Big[\Big(\frac{f'(X)}{f(X)}\Big)^2\Big]=\int_{\mathbb R}\Big(\frac{f'(x)}{f(x)}\Big)^2 f(x)\,dx, $$
--
--   and, for a proposal scale $l$,
--
--   $$ h(l) = 2l^2\,\Phi\Big(-\frac{l\sqrt I}{2}\Big),\qquad a(l) = 2\,\Phi\Big(-\frac{l\sqrt I}{2}\Big). $$
--
--   $h(l)$ is the speed of the limiting Langevin diffusion of Theorem 1.1 and $a(l)$ the limit of the average acceptance rates in Corollary 1.2. Both depend on $f$ only through $I$, so they are also provided as functions $h_I(l)$, $a_I(l)$ of an arbitrary constant $I$; with $I$ the roughness of $f$ they are $h(l)$ and $a(l)$.
--
--   **Formalization Note** $\Phi$ is `cdf (gaussianReal 0 1)`. Under the standing hypotheses (A1) makes $(f'/f)^2 f$ integrable, so $I$ is a genuine integral, not a default value.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 112, Theorem 1.1 (definitions of h(l), Φ and I) and definition of a(l)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace Roberts1997.RWM

/-- The standard normal cumulative distribution function `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The roughness constant `I = 𝔼_f[(f'(X)/f(X))²] = ∫ (f'/f)² f dx`. -/
noncomputable def fisherI (f : ℝ → ℝ) : ℝ := ∫ x, (deriv f x / f x) ^ 2 * f x

/-- `h(l) = 2 l² Φ(-l √I / 2)` as a function of the constant `I`. -/
noncomputable def speedI (I l : ℝ) : ℝ := 2 * l ^ 2 * Phi (-(l * Real.sqrt I) / 2)

/-- `a(l) = 2 Φ(-l √I / 2)` as a function of the constant `I`. -/
noncomputable def accRateI (I l : ℝ) : ℝ := 2 * Phi (-(l * Real.sqrt I) / 2)

/-- The speed `h(l) = 2 l² Φ(-l √I / 2)` of the limiting diffusion, with `I = fisherI f`. -/
noncomputable def speed (f : ℝ → ℝ) (l : ℝ) : ℝ := speedI (fisherI f) l

/-- The limiting acceptance rate `a(l) = 2 Φ(-l √I / 2)`, with `I = fisherI f`. -/
noncomputable def accRate (f : ℝ → ℝ) (l : ℝ) : ℝ := accRateI (fisherI f) l

end Roberts1997.RWM


