-- Prove2me | Definitions.Def_ModelRiskOT_Duality_extIntegral
-- name    : ModelRiskOT_Duality_extIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:53:42.496119+00:00
-- url     : https://prove2.me/theorems/64147db5-f432-422e-9784-68f1aae3140f
-- title:
--   Integral of an extended-real function, $\int\varphi^+\,d\nu-\int\varphi^-\,d\nu$
-- statement:
--   Let $\nu$ be a measure on a measurable space $X$ and $\varphi : X\to[-\infty,\infty]$. Its integral is
--
--   $$\int\varphi\,d\nu \;=\; \int\varphi^+\,d\nu-\int\varphi^-\,d\nu \in [-\infty,\infty],$$
--
--   where $\varphi^+=\max(\varphi,0)$ and $\varphi^-=\max(-\varphi,0)$ and both integrals are Lebesgue integrals of nonnegative functions with values in $[0,\infty]$. If both are infinite the value is $-\infty$ (the convention $\infty-\infty=-\infty$ of extended-real subtraction).
--
--   This one operation gives both the primal objective $I(\pi)=\int f(y)\,d\pi(x,y)$ and the term $\int\varphi\,d\mu$ of the dual objective. With the $-\infty$ convention a measure with $\int f^+=\int f^-=\infty$ never raises a supremum, which is the reading of the supremum in footnote 2 of the paper: $\sup\{\int f\,d\nu : d_c(\mu,\nu)\le\delta,\ \int f^-d\nu<\infty\}$.
--
--   **Formalization Note** The nonnegative integrals are Mathlib's `lintegral`. For a $\nu$-null-measurable $\varphi$ (in particular a universally measurable one) it coincides with the integral against the completion of $\nu$, which is how the paper interprets $\int\varphi\,d\mu$ (p. 4).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 4 (integral against the completion), p. 5 (footnote 2), p. 6

import Mathlib

namespace ModelRiskOT.Duality

open MeasureTheory

/-- The integral of an extended-real function `φ : X → [-∞, ∞]` against a measure `ν`, as
`∫ φ⁺ dν − ∫ φ⁻ dν` computed in `EReal`, with lower Lebesgue integrals of the positive part
`φ⁺ = max(φ, 0)` and the negative part `φ⁻ = max(−φ, 0)`.

Conventions (Blanchet & Murthy, arXiv:1604.01446v2, pp. 4–6 and footnote 2):
* if exactly one of the two parts is infinite, the value is `+∞` or `−∞` accordingly;
* if both are infinite (the paper's "∞ − ∞"), the value is `⊤ - ⊤ = ⊥` in Mathlib's `EReal`
  (`EReal` subtraction is `a + (-b)` and `⊤ + ⊥ = ⊥`), so such a term never raises a supremum;
* for a `ν`-null-measurable `φ` (e.g. a universally measurable one) `lintegral` agrees with the
  integral against the completion of `ν`, which is how the paper reads `∫ φ dμ` (p. 4). -/
noncomputable def extIntegral {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → EReal) :
    EReal :=
  ((∫⁻ x, (φ x).toENNReal ∂ν : ENNReal) : EReal) - ((∫⁻ x, (-φ x).toENNReal ∂ν : ENNReal) : EReal)

end ModelRiskOT.Duality


