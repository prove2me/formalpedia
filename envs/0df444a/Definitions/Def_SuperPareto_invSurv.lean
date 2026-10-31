-- Prove2me | Definitions.Def_SuperPareto_invSurv
-- name    : SuperPareto_invSurv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:19.113995+00:00
-- url     : https://prove2.me/theorems/314b8ccf-7a56-4e54-a87a-d98ec417dfa4
-- title:
--   Proposition 1, p.5 — the reciprocal survival function $g(x)=1/P(X>x)$
-- statement:
--   For a real random variable $X$ on $(\Omega,\mathcal F,P)$ define
--
--   $$
--   g(x)=\frac{1}{P(X>x)},\qquad x\in\mathbb R .
--   $$
--
--   Proposition 1 of the paper characterizes super-Pareto laws by the shape of $g$ (strictly increasing and concave from the essential infimum on), and step (d) of the proof of Theorem 1 uses the scaling of $g$. Below the essential infimum of $X$, $g=1$. For $Y\sim\mathrm{Pareto}(1)$, $g(x)=x$ for $x\ge1$.
--
--   **Formalization Note** $g$ is real-valued and defined on all of $\mathbb R$, with $P(X>x)$ the real probability `P.real`. Where $P(X>x)=0$ Lean's division by zero gives $g(x)=0$ instead of $+\infty$; this happens only at or above an essential upper bound of $X$, so never for a super-Pareto $X$.
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Proposition 1, p.5; §2.3 step (d), p.10

import Mathlib

open MeasureTheory

namespace SuperPareto

/-- **Reciprocal survival function** `g(x) = 1 / P(X > x)`. Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, Proposition 1, p.5 ("the function
`g : x ↦ 1/P(X > x)`") and §2.3, step (d), p.10.

**Formalization Note.** `g` is real-valued and defined on all of `ℝ`, with `P(X > x)` the real
probability `P.real`. Where `P(X > x) = 0` Lean's division gives `g x = 0` (the paper would read
`+∞`); this happens only for `x` at or above an essential upper bound of `X`. Below the essential
infimum of `X`, `g x = 1`. -/
noncomputable def invSurv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) :
    ℝ :=
  1 / P.real {ω | x < X ω}

end SuperPareto


