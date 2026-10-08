-- Prove2me | Definitions.Def_OTDRO_WorstCase_ExampleLoss
-- name    : OTDRO_WorstCase_ExampleLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:01.969543+00:00
-- url     : https://prove2.me/theorems/5f081d29-d784-4c31-a618-45553b8447f9
-- title:
--   Proof of Theorem 6(d), p. 40 — the loss ℓ(u) = u² − |u|(1 − e^{−|u|})
-- statement:
--   The loss of the counterexample used for Theorem 6(d):
--   $$\ell(u)=u^2-|u|\bigl(1-e^{-|u|}\bigr),\qquad u\in\mathbb R .$$
--   It is convex and even, it lies strictly below $u^2$ for $u\ne0$, and $\ell(u)-u^2\to-\infty$ only linearly, so its quadratic growth exponent is exactly $\kappa=1$. These features make the dual optimum equal to the threshold $\lambda_{thr}$ while the primal worst case is not attained.
-- source:
--   arXiv:1810.02403v3, §5.4, proof of Theorem 6(d), p. 40

import Mathlib

namespace OTDRO.WorstCase

/-- The loss of the counterexample in the proof of Theorem 6(d)
(arXiv:1810.02403v3, §5.4, p. 40): `ℓ(u) = u² − |u|(1 − e^{−|u|})`. -/
noncomputable def exampleLoss (u : ℝ) : ℝ :=
  u ^ 2 - |u| * (1 - Real.exp (-|u|))

end OTDRO.WorstCase


