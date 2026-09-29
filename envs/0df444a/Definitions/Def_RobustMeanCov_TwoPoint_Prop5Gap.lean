-- Prove2me | Definitions.Def_RobustMeanCov_TwoPoint_Prop5Gap
-- name    : RobustMeanCov_TwoPoint_Prop5Gap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:48:53.360983+00:00
-- url     : https://prove2.me/theorems/75f10751-2c42-4ae6-ab56-af5ec806e9b4
-- title:
--   The auxiliary function $g$ of the proof of Proposition 5 (Popescu 2007)
-- statement:
--   Fix $u:\mathbb R\to\mathbb R$, $\mu\in\mathbb R$ and $\sigma>0$. For $y<\mu$ let $z=\mu+\sigma^2/(\mu-y)$ (the **partner point**), and
--   $$
--   g(y)=\frac{u(z)-u(y)}{z-y}-\frac{u'(y)+u'(z)}{2}.
--   $$
--   For $y<\mu$ one has $z>\mu>y$ and $(z-\mu)(\mu-y)=\sigma^2$; a zero $a$ of $g$ together with its partner $b=z$ satisfies conditions (a) and (b) of Lemma 1 with $q_a=u'(a)$, $q_b=u'(b)$.
--
--   **Formalization Note** `partnerPoint μ σ y` is $\mu+\sigma^2/(\mu-y)$ and `prop5Gap u μ σ y` is $g(y)$, with $u'$ written `deriv u`. Both are defined for every real $y$ but only used for $y<\mu$ (as $y\to-\infty$, as $y\to\mu^-$, or at a point with $y<\mu$).
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 5 (definition of g)

import Mathlib

namespace RobustMeanCov.TwoPoint

/-- The partner point `z = μ + σ² / (μ - y)` of the proof of Proposition 5 (Popescu 2007,
Appendix, p. 110); meaningful for `y < μ`. -/
noncomputable def partnerPoint (μ σ y : ℝ) : ℝ :=
  μ + σ ^ 2 / (μ - y)

/-- The function `g(y) = (u(z) - u(y)) / (z - y) - (u'(y) + u'(z)) / 2` with
`z = μ + σ² / (μ - y)`, from the proof of Proposition 5 (Appendix, p. 110); meaningful for
`y < μ`. -/
noncomputable def prop5Gap (u : ℝ → ℝ) (μ σ y : ℝ) : ℝ :=
  (u (partnerPoint μ σ y) - u y) / (partnerPoint μ σ y - y) -
    (deriv u y + deriv u (partnerPoint μ σ y)) / 2

end RobustMeanCov.TwoPoint


