-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_stdCauchy
-- name    : KallMayerSLP_NormalCC_stdCauchy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:57.667721+00:00
-- url     : https://prove2.me/theorems/829a994f-d15b-4e8e-b2f5-ca43a32ae5b8
-- title:
--   Standard Cauchy distribution $\mathcal C(0,1)$
-- statement:
--   The **standard Cauchy distribution** $\mathcal C(0,1)$ is the probability distribution on $\mathbb R$ with density
--   $$\psi(x)=\frac1\pi\,\frac1{1+x^2},\qquad -\infty<x<\infty,$$
--   the Cauchy density $f(x)=\frac1\pi\frac{t}{t^2+(x-m)^2}$ with location $m=0$ and scale $t=1$. Its distribution function is denoted $\Psi$. It has no expected value, but it is strictly stable and symmetric, which makes the chance constraints of §2.3.3 tractable.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, §2.3.3, p.115 (PDF p.125)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.NormalCC

/-- **The standard Cauchy distribution `𝒞(0, 1)`** (Kall & Mayer 2005, Chapter 2, §2.3.3, p.115,
PDF p.125): the probability distribution on `ℝ` with density
`ψ(x) = (1/π) · 1/(1 + x²)`, `−∞ < x < ∞` (the Cauchy density `f(x) = (1/π) t/(t² + (x − m)²)`
with location `m = 0` and scale `t = 1`).

**Formalization Note.** Defined as Lebesgue measure with density `ψ` (`withDensity`, density
converted to `ℝ≥0∞` by `ENNReal.ofReal`; `ψ > 0`, so nothing is truncated). -/
noncomputable def stdCauchy : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (1 / (Real.pi * (1 + x ^ 2))))

end KallMayerSLP.NormalCC


