-- Prove2me | Definitions.Def_FDivToolkit_IsRefModel
-- name    : FDivToolkit_IsRefModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:49.103372+00:00
-- url     : https://prove2.me/theorems/47bc2a5c-bf6a-4f3e-a971-b60d0fc0da18
-- title:
--   Reference model $\nu$ with density $f$ and support $\mathcal S$
-- statement:
--   The **reference model** $\nu$ is a distribution on $\mathbb R$ with density $f$ such that
--   $$
--   \int_{\mathcal S}|x|\,f(x)\,dx<\infty,
--   $$
--   where $\mathcal S\subseteq\mathbb R$, bounded or unbounded, is the support of $\nu$, and $f(x)=0$ for $x\in\mathbb R\setminus\mathcal S$.
--
--   Everything in the mission is stated relative to such a model.
--
--   **Formalization Note** $\mathcal S$ is the closed support, Mathlib's `Measure.support` of `densityMeasure f`: the points all of whose neighbourhoods have positive $\nu$-measure.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, p.5, and footnote 2

import Definitions.Def_FDivToolkit_IsDensity

open MeasureTheory

namespace FDivToolkit

/-- The support `𝓢 ⊆ ℝ` of the distribution ν with density `f` (Kruse, Schneider & Schweizer,
SSRN 3680475 (Aug 25, 2020), §2.1, p.5).

**Formalization Note.** This is the closed support, Mathlib's `Measure.support`: the points all of
whose neighbourhoods have positive ν-measure. A larger set carrying ν would not do, since
Proposition 1 distinguishes `sup 𝓢 = ∞`. -/
noncomputable def refSupport (f : ℝ → ℝ) : Set ℝ :=
  (densityMeasure f).support

/-- The standing assumptions on the reference model ν (Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), §2.1, p.5): ν has a density `f` with `∫_𝓢 |x| f(x) dx < ∞`, and "`f(x) = 0` for
`x ∈ ℝ \ 𝓢`" (footnote 2).

**Formalization Note.** ν is `densityMeasure f`. The integral over `𝓢` is an integral over `ℝ`
because `f` vanishes off `𝓢`. Finiteness of a nonnegative integral is `Integrable`. -/
structure IsRefModel (f : ℝ → ℝ) : Prop extends IsDensity f where
  integrable_abs_mul : Integrable fun x => |x| * f x
  eq_zero_of_notMem : ∀ x, x ∉ refSupport f → f x = 0

end FDivToolkit


