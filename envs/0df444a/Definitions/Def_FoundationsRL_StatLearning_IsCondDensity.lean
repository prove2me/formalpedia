-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_IsCondDensity
-- name    : FoundationsRL_StatLearning_IsCondDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:40.53401+00:00
-- url     : https://prove2.me/theorems/309ca43d-876a-481b-b96a-7efd8ba6f2d7
-- title:
--   Conditional density $f(\cdot\mid x)$
-- statement:
--   Let $\nu$ be a reference measure on $\mathcal Y$. A jointly measurable function $f:\mathcal X\times\mathcal Y\to[0,\infty)$ is a **conditional density** if for every $x$
--
--   $$
--   \int f(y\mid x)\,\nu(dy)=1.
--   $$
--
--   These are the predictors $f:\mathcal X\to\mathcal Y'=\Delta(\mathcal Y)$ of conditional density estimation, and $\ell_{\log}(f(x),y)=-\log f(y\mid x)$.
--
--   **Formalization Note** The notes leave the reference measure implicit. Counting measure on a countable $\mathcal Y$ gives the discrete case.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, p. 7; Remark 1, p. 8

import Mathlib
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Conditional density** `f(·|x)`: for each feature `x`, `f x` is a probability density on `Y`
with respect to the reference measure `ν`. These are the predictors `f : X → Y' = Δ(Y)` of
conditional density estimation.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, p. 7, and Remark 1, p. 8.

**Formalization Note.** The notes write `Y' = Δ(Y)` and "the negative log of the conditional
density"; the reference measure stays implicit, and here it is the parameter `ν`. Taking `ν` the
counting measure on a countable `Y` gives the discrete case `f(y|x) = f(x)(y)`. Densities are
real-valued and nonnegative, and jointly measurable in `(x, y)`. -/
def IsCondDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure Y)
    (f : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ f x y) ∧ Measurable (fun p : X × Y => f p.1 p.2) ∧
    ∀ x, ∫⁻ y, ENNReal.ofReal (f x y) ∂ν = 1

end FoundationsRL.StatLearning


