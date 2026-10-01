-- Prove2me | Definitions.Def_ChapterGaugeCasimirAverage
-- name    : ChapterGaugeCasimirAverage
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:59:01.404575+00:00
-- url     : https://prove2.me/theorems/92ecf598-8f4f-4ff5-96ef-c124b2ab4ceb
-- title:
--   Chapter GaugeCasimirAverage
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeCasimirAverage.lean`): generated def bundle for ChapterGaugeCasimirAverage. See BookProof/ChapterGaugeCasimirAverage.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeCasimirAverage.lean

import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib


/-!
# Casimir constraints, Haar averaging and the pushforward of the constrained measure

This module formalizes the three remaining analytic claims of the section
*"Gauge transformations, constrained systems and conditioned probability"* of
`book.tex` (lines 2221–2400), which the companion modules
`BookProof.ChapterGaugeIncompleteFixing` and
`BookProof.ChapterGaugeComprehensiveFixing` do not cover.

## 1. Casimir constraints (`book.tex` 2383–2387)

> "Note that it suffices to constrain to zero the Casimir operators of the
> (eventually non-commutative) Lie algebra of constraints, this imposes the
> constraints without the need for the constraints to be part of the commutative
> von Neumann algebra, only the Casimir operators are included in the commutative
> algebra."

For symmetric (Hermitian) constraint generators `T a`, the quadratic Casimir
`C = ∑ a, T a ∘ T a` satisfies `⟪v, C v⟫ = ∑ a, ‖T a v‖²` (`inner_casimir`), so
`C v = 0` **iff** every constraint annihilates `v`
(`casimir_apply_eq_zero_iff`); equivalently `ker C = ⨅ a, ker (T a)`
(`ker_casimir`).  Constraining the single operator `C` to zero therefore imposes
all the constraints at once, exactly as the book asserts.

## 2. The Haar average produces the gauge-invariant functional (`book.tex` 2377)

> "for a locally compact gauge group (a Lie group, for instance), a constant
> measure (Haar measure) always exists which allows to create a functional which
> is gauge invariant."

`gaugeAverage μ f x = ∫ g, f (g • x) ∂μ` is a physical (gauge-invariant)
observable as soon as `μ` is right invariant (`gaugeAverage_isPhysicalObservable`),
it is normalized on the constants when `μ` is a probability measure
(`gaugeAverage_const`), and it fixes the observables that are already physical
(`gaugeAverage_of_isPhysicalObservable`) — so averaging is a projection onto the
physical algebra, and the "constrained spectrum" of gauge-invariant functionals is
never empty.  The same three facts are proved for a finite gauge group with the
normalized counting average (`finiteGaugeAverage_*`), where no integrability
hypothesis at all is needed.

Between the two, `isPhysicalObservable_of_tendsto` records the manuscript's remark
that a *gauge* symmetry can never be anomalous (`book.tex` 2389–2395): gauge
invariance of the observables survives every limit, so no symmetry-breaking
parameter can destroy it.

## 3. The pushforward implements the exact constraint without a null set
(`book.tex` 2228–2238 and 2369–2376)

> "there is still the possibility of defining the probability measure of the
> constrained space as a pushforward measure from the unconstrained to the
> constrained space" … "Then, the pushforward measure using such measurable
> function implements the exact constraints in a separable probability space
> without attributing to the constrained space null probability measure."

`map_measure_constrainedSet` : for a measurable projection `q` of the spectrum
into the constrained set `C`, the pushforward `μ.map q` gives `C` probability one
— the exact constraint holds almost surely, and the constrained space carries the
whole measure instead of being null.  `integral_map_of_invariant` : expectation
values of the observables that do not see the projection (in particular the
physical ones, when the projection moves a point only inside its gauge
equivalence class) are unchanged by the pushforward.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterGaugeCasimirAverage

open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

/-! ## 1. Casimir operator of a family of constraints -/

section Casimir

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]

/-- The quadratic Casimir operator `∑ a, T a ∘ T a` of a finite family of
constraint generators `T`. -/
noncomputable def casimir (T : ι → V →ₗ[ℂ] V) : V →ₗ[ℂ] V := ∑ a, (T a) ∘ₗ (T a)









end Casimir

/-! ## 2. Haar averaging: the gauge-invariant functional -/

section Averaging

variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]

/-- The **Haar average** of an observable over the gauge group: the book's
"functional which is gauge invariant" built from the constant (Haar) measure. -/
noncomputable def gaugeAverage (μ : Measure G) (f : X → ℝ) (x : X) : ℝ :=
  ∫ g, f (g • x) ∂μ







end Averaging

/-! ### The finite gauge group: averaging with no integrability hypothesis -/

section FiniteAveraging

variable {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]

/-- The normalized average of an observable over a finite gauge group. -/
noncomputable def finiteGaugeAverage (G : Type*) [Group G] [Fintype G] [MulAction G X]
    (f : X → ℝ) (x : X) : ℝ :=
  (∑ g : G, f (g • x)) / (Fintype.card G)







end FiniteAveraging

/-! ### No anomaly for a gauge symmetry (`book.tex` 2389–2395) -/

section NoAnomaly

variable {X : Type*} {G : Type*} [Group G] [MulAction G X]



end NoAnomaly

/-! ## 3. The pushforward measure implements the exact constraint -/

section Pushforward

variable {X : Type*} [MeasurableSpace X]







end Pushforward

end BookProof.ChapterGaugeCasimirAverage


