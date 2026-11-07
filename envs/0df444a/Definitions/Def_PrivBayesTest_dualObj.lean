-- Prove2me | Definitions.Def_PrivBayesTest_dualObj
-- name    : PrivBayesTest_dualObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:54.405263+00:00
-- url     : https://prove2.me/theorems/8c80972d-b28e-4caf-8577-713b6215e254
-- title:
--   Dual objective $G_\alpha(\varphi)$
-- statement:
--   For probability measures $P,Q$ on $\mathcal X$, $\alpha\in(0,1)$ and a function $\varphi:\mathcal X\to\mathbb R$, the **dual objective** is
--
--   $$
--   G_\alpha(\varphi) \;=\; -\alpha\log\int e^{-\varphi/\alpha}\,dP \;-\;(1-\alpha)\log\int e^{\varphi/(1-\alpha)}\,dQ .
--   $$
--
--   Lemma 2.4 identifies $\inf_{R,S}F_\alpha$ with the supremum of $G_\alpha$ over $\|\varphi\|_\infty\le\tilde\alpha\varepsilon/2$.
--
--   **Formalization Note** The integrals are lower integrals with values in $(0,\infty]$, and the result is an extended real; each term lies in $[-\infty,\infty)$, so no $\infty-\infty$ arises. For bounded measurable $\varphi$ both integrals are finite and $G_\alpha(\varphi)$ is the real number of the paper.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 2.4 and Proposition 2.5, p.10

import Mathlib

open MeasureTheory

namespace PrivBayesTest

/-- The **dual objective**
`G_α(φ) = −α log ∫ e^{−φ/α} dP − (1 − α) log ∫ e^{φ/(1−α)} dQ`
of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Lemma 2.4 and Proposition 2.5, p.10.

**Formalization Note** The integrals are lower integrals of `ENNReal.ofReal (exp …)`, with values in
`(0, ∞]` for probability measures, and the logarithm is `ENNReal.log` into `EReal`. Each of the two
terms then lies in `[−∞, ∞)`, so no `∞ − ∞` arises. For bounded measurable `φ` (the paper's dual
variables) both integrals are finite and `G_α(φ)` is the real number of the paper. -/
noncomputable def dualObj {X : Type*} [MeasurableSpace X] (P Q : Measure X) (α : ℝ) (φ : X → ℝ) :
    EReal :=
  -((α : ℝ) : EReal) * ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (-φ x / α)) ∂P)
    - ((1 - α : ℝ) : EReal) * ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (1 - α))) ∂Q)

end PrivBayesTest


