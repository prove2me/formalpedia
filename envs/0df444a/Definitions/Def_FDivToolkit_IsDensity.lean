-- Prove2me | Definitions.Def_FDivToolkit_IsDensity
-- name    : FDivToolkit_IsDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:05.031504+00:00
-- url     : https://prove2.me/theorems/5c111092-b9c9-4fe7-a50d-f5cc3b0ad3de
-- title:
--   Probability densities on $\mathbb R$
-- statement:
--   A **density** is a nonnegative measurable function $g:\mathbb R\to\mathbb R$ with $\int_{\mathbb R} g(x)\,dx=1$, density always being meant with respect to Lebesgue measure. It determines the distribution $\eta$ with $\eta(A)=\int_A g(x)\,dx$.
--
--   The paper uses every model only through its density, so the mission represents a model by its density and writes `densityMeasure g` for the distribution.
--
--   **Formalization Note** The Bochner integral of a non-integrable function is $0$, so the equation $\int g=1$ also forces integrability.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, footnote 2, p.5

import Mathlib

open MeasureTheory

namespace FDivToolkit

/-- The measure on `ℝ` with density `g` with respect to Lebesgue measure.
Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, footnote 2, p.5: "By density we
always mean density with respect to the Lebesgue measure on ℝ."

**Formalization Note.** The paper only ever uses its distributions through their densities, so a
model is represented by a density `g`, and the distribution by `densityMeasure g`. -/
noncomputable def densityMeasure (g : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (g x)

/-- `g` is a probability density on `ℝ`: the density of a distribution η (Kruse, Schneider &
Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, p.5, and footnote 2).

**Formalization Note.** Nonnegative and measurable everywhere, with total integral `1`. Since the
Bochner integral of a non-integrable function is `0`, the equation `∫ g = 1` also forces `g` to be
integrable. -/
structure IsDensity (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  measurable : Measurable g
  integral_eq_one : ∫ x, g x = 1

end FDivToolkit


