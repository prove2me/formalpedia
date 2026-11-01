-- Prove2me | Definitions.Def_ConvBoundsQA_AdmitsDecDensity
-- name    : ConvBoundsQA_AdmitsDecDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:16.322371+00:00
-- url     : https://prove2.me/theorems/a90141d3-8189-4de5-9dba-a1e9874ef75f
-- title:
--   Admitting a decreasing (increasing) density
-- statement:
--   A distribution $\rho\in\mathcal M$ **admits a decreasing density** if its support is bounded below and it has a decreasing probability density with respect to Lebesgue measure on its support: there are $a\in\mathbb R$ and a measurable $f\ge0$ with $f=0$ on $(-\infty,a)$, $f$ non-increasing on $(a,\infty)$, and $\rho(\mathrm dx)=f(x)\,\mathrm dx$. Symmetrically, $\rho$ **admits an increasing density** if there are $b\in\mathbb R$ and a measurable $f\ge0$ with $f=0$ on $(b,\infty)$, $f$ non-decreasing on $(-\infty,b)$, and $\rho(\mathrm dx)=f(x)\,\mathrm dx$.
--
--   These are the shape conditions under which the convolution bounds are sharp.
--
--   **Formalization Note** "Decreasing" means non-increasing. The density takes values in $[0,\infty]$ and may be unbounded at $a$ (e.g. $x^{-1/2}$ on $(0,1]$); the support is the interval where $f$ is positive.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §4, p.9

import Mathlib

open MeasureTheory

namespace ConvBoundsQA

/-- `ρ` admits a decreasing density: its support is bounded below by some `a` and it has a density
with respect to Lebesgue measure that is decreasing on the support
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §4, p.9: "the distribution has a left-bounded
support and it has a decreasing probability density function with respect to the Lebesgue measure
on its support").

**Formalization Note** "Decreasing" is non-increasing. The density `f` vanishes on `(−∞, a)` and is
non-increasing on `(a, ∞)`; the open half-line lets `f` be unbounded at `a` (e.g. `x^{−1/2}` on
`(0, 1]`), and the support `[a, b]` or `[a, ∞)` is the interval on which `f` is positive. -/
def AdmitsDecDensity (ρ : Measure ℝ) : Prop :=
  ∃ a : ℝ, ∃ f : ℝ → ENNReal, Measurable f ∧ (∀ x, x < a → f x = 0) ∧
    AntitoneOn f (Set.Ioi a) ∧ ρ = volume.withDensity f

/-- `ρ` admits an increasing density: the mirror image of `AdmitsDecDensity`, with support bounded
above by some `b` and a density that is non-decreasing on `(−∞, b)`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §4, p.9: "The case for 'admitting an increasing
density' is analogous").

**Formalization Note** "Increasing" is non-decreasing. -/
def AdmitsIncDensity (ρ : Measure ℝ) : Prop :=
  ∃ b : ℝ, ∃ f : ℝ → ENNReal, Measurable f ∧ (∀ x, b < x → f x = 0) ∧
    MonotoneOn f (Set.Iio b) ∧ ρ = volume.withDensity f

end ConvBoundsQA


