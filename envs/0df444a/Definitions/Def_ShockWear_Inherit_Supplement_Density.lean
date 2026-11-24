-- Prove2me | Definitions.Def_ShockWear_Inherit_Supplement_Density
-- name    : ShockWear_Inherit_Supplement_Density
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:49:13.725041+00:00
-- url     : https://prove2.me/theorems/eba77122-f73d-41f1-bd72-2724c88b8869
-- title:
--   Chosen probability-density versions with respect to Lebesgue measure
-- statement:
--   A chosen density of a probability law $\mu$ is a nonnegative, Lebesgue-measurable real function $f$ that induces that law:
--
--   $$
--   \mu(A)=\int_A f(x)\,dx
--   $$
--
--   for every measurable set $A$. Its pointwise values specify the version to which the source's PF₂ condition is applied. The probability-law and nonnegative-support assumptions are stated on the theorems, separately from this representation.
--
--   This interface connects the density assumptions of Theorems 4.8, 5.4 and 5.5 to the published convolution model. It imposes no moments, smoothness, strict positivity, or bounded support.
--
--   **Formalization Note** `AEMeasurable f volume` permits Lebesgue-measurable versions, and equality with `volume.withDensity (ENNReal.ofReal ∘ f)` fixes the entire law. Probability normalization is supplied by `IsProbabilityMeasure μ`, so divergent or non-integrable functions cannot serve as probability densities.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 630–632, Definition 2.3 and ageing definitions; https://doi.org/10.1214/aop/1176996891

import Mathlib

namespace ShockWear.Inherit.Supplement

open MeasureTheory

/-- A chosen nonnegative Lebesgue-measurable real version of a density.
No moments or pointwise strict positivity are imposed. -/
def IsDensity (μ : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x))

end ShockWear.Inherit.Supplement


