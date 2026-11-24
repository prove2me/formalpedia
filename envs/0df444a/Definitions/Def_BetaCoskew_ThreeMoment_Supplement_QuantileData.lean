-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Supplement_QuantileData
-- name    : BetaCoskew_ThreeMoment_Supplement_QuantileData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:37:01.872703+00:00
-- url     : https://prove2.me/theorems/bfd4ad67-b686-46d4-aa60-c7c12462f70b
-- title:
--   §2.2, p. 10 — strict lower quantile, dual weighting and the tail function N
-- statement:
--   Let $\mu$ be the law of the positive integrable pricing kernel, with cumulative distribution function $F$. Its lower quantile, the dual probability weighting, and the tail function are
--
--   $$
--   Q^-_\mu(p)=\sup\{x\in\mathbb R:F(x)<p\},\qquad
--   \bar w(p)=1-w(1-p),\qquad
--   N(q)=-\int_{\bar w^{-1}(q)}^{1-}Q^-_\mu(1-p)\,dp,\quad q\in[0,1].
--   $$
--   The inverse is taken on $[0,1]$. These objects enter the concave-envelope construction of the optimal payoff.
--
--   **Formalization Note** The quantile is first computed in the extended reals: its value at level zero is $-\infty$, and at level one it can be $+\infty$. Its real conversion is used only at interior levels in open-interval Lebesgue integrals. The kernel assumptions ensure that the tail integrals defining $N$ are integrable, so their Bochner representation has no default-value effect. The improper endpoint $1-$ is implemented by an open upper endpoint; no bounded support is required.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 10, §2.2, definition preceding Theorem 1

import Mathlib

namespace BetaCoskew.ThreeMoment.Supplement

open MeasureTheory ProbabilityTheory Set

/-- The source's strict lower quantile, including the extended endpoint at 1.
The empty set has supremum -∞ and an unbounded set has supremum +∞. -/
noncomputable def lowerQuantileE (μ : Measure ℝ) (p : ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' {x : ℝ | cdf μ x < p})

/-- Real quantile used only at interior levels in Lebesgue integrals.
At extended endpoints the conversion returns 0; those endpoints are excluded. -/
noncomputable def lowerQuantile (μ : Measure ℝ) (p : ℝ) : ℝ :=
  (lowerQuantileE μ p).toReal

/-- Dual probability weighting w̄. -/
def dualWeight (w : ℝ → ℝ) (p : ℝ) : ℝ := 1 - w (1 - p)

/-- The inverse of w̄ restricted to [0,1]. The weighting assumptions make this
an actual inverse on [0,1]; values outside that range are unused. -/
noncomputable def dualInverse (w : ℝ → ℝ) (q : ℝ) : ℝ :=
  Function.invFunOn (dualWeight w) (Icc 0 1) q

/-- N(q) on [0,1], p.10. The open upper endpoint implements 1−. The kernel's
positive integrable law makes every such tail integral genuine. -/
noncomputable def tailN (μ : Measure ℝ) (w : ℝ → ℝ) (q : ℝ) : ℝ :=
  -(∫ p in Ioo (dualInverse w q) 1, lowerQuantile μ (1 - p))

end BetaCoskew.ThreeMoment.Supplement


