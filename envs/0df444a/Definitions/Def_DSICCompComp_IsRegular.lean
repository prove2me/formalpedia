-- Prove2me | Definitions.Def_DSICCompComp_IsRegular
-- name    : DSICCompComp_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:04.123056+00:00
-- url     : https://prove2.me/theorems/f59d7e78-abd1-4e94-81ef-ce27448d80aa
-- title:
--   Regular value distribution (positive density, nondecreasing virtual value)
-- statement:
--   A probability distribution $D$ of a nonnegative value is **regular** if it has a density $f$ and its **virtual value**
--   $$
--   \varphi(v) = v - \frac{1 - F(v)}{f(v)}
--   $$
--   is nondecreasing, where $F$ is the CDF of $D$. Following the standard convention, the density is required to be positive (and finite) on an interval $I$ that carries all of the mass, and $\varphi$ is required to be nondecreasing on $I$, where it is defined.
--
--   A product distribution $D = D_1 \times \cdots \times D_m$ is regular when every marginal $D_j$ is regular. Regularity is the hypothesis under which Myerson's optimal auction for a single item is a second-price auction with a reserve price.
--
--   **Formalization Note** $D$ is a measure on $\mathbb R_{\ge 0}$; its CDF and density are those of its pushforward to $\mathbb R$, the density is taken with respect to Lebesgue measure and is any measurable version (densities are only defined up to null sets). This is the definition of Section 2, which is narrower than the concave-revenue-curve definition of footnote 1. No bounded support and no finite mean are required: the distribution used in Section 3.2 has an equal-revenue tail and infinite mean.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.5 (pdf p.6)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- A **regular** univariate value distribution (Ryu–Weinberg–Xue, *The DSIC Competition
Complexity of Additive Buyers over Independent Items*, STOC 2027 submission, manuscript of
Nov. 3, 2026, sha256 bf61bfdb…, Section 2, p.5 (pdf p.6)): the distribution has a density `f`
and the virtual value `φ(v) = v − (1 − F(v))/f(v)` is nondecreasing, where `F` is the CDF.

Lean reading: `μ` is a probability measure on `ℝ≥0`; its pushforward to `ℝ` has a measurable
density `f` (w.r.t. Lebesgue measure); there is an interval `I` (an order-connected set) that
carries all of the mass, on which `0 < f < ∞`; and `v ↦ v − (1 − F(v))/f(v)` is monotone on `I`,
with `F = cdf (μ.map (↑))`.

**Formalization Note** This is Section 2's density / virtual-value definition, read with the
standard convention that a regular distribution has a positive density on an interval support
(the virtual value is only defined where `f > 0`). It is narrower than footnote 1's concave
revenue curve. No bounded support and no finite mean is required. Values are nonnegative reals,
so `μ` lives on `ℝ≥0` and regularity is read through the pushforward to `ℝ`. -/
def IsRegular (μ : Measure ℝ≥0) : Prop :=
  IsProbabilityMeasure μ ∧
    ∃ (f : ℝ → ℝ≥0∞) (I : Set ℝ), Measurable f ∧
      μ.map (fun x : ℝ≥0 => (x : ℝ)) = volume.withDensity f ∧
      I.OrdConnected ∧ μ.map (fun x : ℝ≥0 => (x : ℝ)) Iᶜ = 0 ∧
      (∀ x ∈ I, 0 < f x ∧ f x < ⊤) ∧
      MonotoneOn
        (fun v : ℝ => v - (1 - cdf (μ.map (fun x : ℝ≥0 => (x : ℝ))) v) / (f v).toReal) I

end DSICCompComp


