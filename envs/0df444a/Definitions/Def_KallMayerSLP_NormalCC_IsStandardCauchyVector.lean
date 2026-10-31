-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_IsStandardCauchyVector
-- name    : KallMayerSLP_NormalCC_IsStandardCauchyVector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:43.932403+00:00
-- url     : https://prove2.me/theorems/ac8d9d0e-7c31-4369-9b28-409cf610e729
-- title:
--   Vector of independent standard Cauchy random variables
-- statement:
--   An $s$-dimensional random vector $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ whose components are measurable, stochastically independent, and each have the standard Cauchy distribution $\mathcal C(0,1)$.
--
--   It is the driving noise in Definition 2.2 of the multivariate Cauchy distribution.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Definition 2.2, p.115 (PDF p.125)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_stdCauchy

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.NormalCC

/-- **A vector of independent standard Cauchy variables** (Kall & Mayer 2005, Chapter 2,
Definition 2.2, p.115, PDF p.125): "`ζ̃` is an `s`-dimensional random vector with its components
being stochastically independent and `ζ̃_i` having a standard Cauchy distribution, `∀ i`."

**Formalization Note.** Coordinates are given as `ζt : Fin s → Ω → ℝ`: each is measurable, they
are jointly independent (`iIndepFun`), and each has law `stdCauchy` (density
`1/(π(1 + x²))`). This mirrors the platform definition
`HighDimProb.RandomVectors.IsStandardGaussianVector` with the Cauchy law in place of `N(0, 1)`. -/
def IsStandardCauchyVector {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {s : ℕ}
    (ζt : Fin s → Ω → ℝ) : Prop :=
  (∀ j, Measurable (ζt j)) ∧ iIndepFun ζt P ∧ ∀ j, Measure.map (ζt j) P = stdCauchy

end KallMayerSLP.NormalCC


