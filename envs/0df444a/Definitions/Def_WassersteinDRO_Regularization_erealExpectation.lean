-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_erealExpectation
-- name    : WassersteinDRO_Regularization_erealExpectation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:30.183234+00:00
-- url     : https://prove2.me/theorems/692586e8-6ddf-456b-aaba-0251bac64242
-- title:
--   Extended-real expectation with the paper's convention
-- statement:
--   For a measure $Q$ on $E$ and an extended-real-valued function $f : E \to [-\infty,\infty]$, $\operatorname{erealExpectation}(Q,f)$ is the expectation $\mathbb{E}_Q[f]$ with the paper's convention (p. 2): writing $f^+ = \max(f,0)$ and $f^- = \max(-f,0)$, the value is $+\infty$ whenever $\int f^+\,dQ = \infty$ (in particular whenever both parts have infinite integral), and $\int f^+\,dQ - \int f^-\,dQ \in [-\infty,\infty)$ otherwise. For a $Q$-integrable real-valued $f$ this is the Bochner integral $\int f\,dQ$; for a measurable $f$ with exactly one infinite part it is $\pm\infty$. The positive and negative parts are taken as $[0,\infty]$-valued functions via `EReal.toENNReal`, and their integrals are lower Lebesgue integrals, which coincide with the Lebesgue integrals for measurable $f$. Redefined in this chapter's own namespace, mirroring `WassersteinDRO.Duality.erealExpectation` verbatim.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), p. 1–2 (convention for $\mathbb{E}_P[\ell(\xi)]$ stated after eq. (2))

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The expectation `E_Q[f]` of an extended-real-valued function `f` under a measure `Q`,
with the convention of Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein
Distributionally Robust Optimization*, INFORMS TutORials 2019 (arXiv:1908.08729v2), p. 1–2:
"we set `E_P[ℓ(ξ)] = ∞` whenever the expectations of the positive and negative parts of
`ℓ(ξ)` are both infinite." Writing `f⁺ = max(f,0)` and `f⁻ = max(-f,0)` (as `ℝ≥0∞`-valued
functions, via `EReal.toENNReal`), the value is `+∞` whenever `∫ f⁺ dQ = ∞`, and the extended
real number `∫ f⁺ dQ - ∫ f⁻ dQ ∈ [-∞, ∞)` otherwise. For a `Q`-integrable real-valued `f`
this is the Bochner integral `∫ f dQ`. Redefined locally in this chapter's own namespace,
mirroring `WassersteinDRO.Duality.erealExpectation` verbatim; see
`Def_WassersteinDRO_Regularization_wassersteinDistance` for why. -/
noncomputable def erealExpectation {E : Type*} [MeasurableSpace E] (Q : Measure E)
    (f : E → EReal) : EReal :=
  if ∫⁻ x, (f x).toENNReal ∂Q = ⊤ then ⊤
  else ((∫⁻ x, (f x).toENNReal ∂Q : ENNReal) : EReal) -
    ((∫⁻ x, (-(f x)).toENNReal ∂Q : ENNReal) : EReal)

end WassersteinDRO.Regularization


