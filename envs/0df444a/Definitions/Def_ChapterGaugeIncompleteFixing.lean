-- Prove2me | Definitions.Def_ChapterGaugeIncompleteFixing
-- name    : ChapterGaugeIncompleteFixing
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:00:46.270625+00:00
-- url     : https://prove2.me/theorems/3851387d-95d7-44aa-9173-fd56ba0f0539
-- title:
--   Chapter GaugeIncompleteFixing
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeIncompleteFixing.lean`): generated def bundle for ChapterGaugeIncompleteFixing. See BookProof/ChapterGaugeIncompleteFixing.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeIncompleteFixing.lean

import Mathlib


/-!
# Gauge symmetry defined by a *comprehensive but incomplete* gauge fixing

This module formalizes the section *"Gauge transformations, constrained systems
and conditioned probability"* of `book.tex` (lines 2221–2400), and specifically
the argument by which a gauge symmetry can be **defined** at all:

> "Note that it is a subalgebra of the commutative von Neumann algebra that is
> gauge-invariant and not the Hilbert space." (`book.tex` 2260)

> "If we consider instead a commutative von Neumann algebra and its spectrum,
> such that any non-trivial gauge transformation necessarily modifies any point
> of the spectrum while conserving the commutative von Neumann algebra […] then
> such commutative von Neumann algebra is one example of an incomplete
> unconstrained gauge-fixing. […] Such commutative algebra has the crucial
> advantage that the gauge generators are necessarily excluded from the algebra,
> so that it can be used to define a separable Hilbert space compatible with the
> gauge group because the expectation value of any operator of the commutative
> algebra which commutes with the gauge generators is the same at each
> equivalence class." (`book.tex` 2329–2348)

The book's two axes of classification of a gauge fixing are used here with the
book's own vocabulary (`book.tex` 2294–2299, 7406, 7427):

* *comprehensive* — the gauge fixing crosses **at least** once each gauge
  equivalence class (`IsComprehensiveGaugeFixing`);
* *complete* — it crosses **at most** once each class, i.e. there is no remnant
  gauge symmetry (`IsCompleteGaugeFixing'`); the gauge fixing used in the book is
  deliberately **incomplete**;
* *unconstrained* — the gauge generators are excluded from the commutative
  algebra, which here is the condition that every non-trivial gauge
  transformation moves **every** point of the spectrum
  (`MovesEveryPointOfSpectrum`).

The content proved below is:

1. **Spectrum layer.** The full spectrum is a comprehensive gauge fixing
   (`univ_isComprehensiveGaugeFixing`); if every non-trivial gauge transformation
   moves every point (unconstrained), this gauge fixing is necessarily
   *incomplete* (`unconstrained_gauge_fixing_incomplete`), its remnant symmetry
   is a *faithful* representation of the gauge group (`remnant_faithful`), and no
   point of the spectrum is gauge invariant (`no_gauge_invariant_point`).
2. **The physical algebra is nevertheless complete.** Gauge-invariant
   ("physical") observables form a subalgebra (`physicalSubalgebra`), they are
   exactly the functions of the gauge equivalence class
   (`isPhysicalObservable_iff_factors`), two of them that agree on a
   comprehensive gauge fixing are equal (`physical_ext_of_comprehensive`), and
   *every* remnant-invariant observable of a comprehensive gauge fixing is the
   restriction of a physical observable (`exists_physical_extension`). So passing
   to a comprehensive but incomplete gauge fixing loses no physical information.
3. **Hilbert-space layer.** For a unitary representation of the gauge group, the
   physical operators are the commutant (`isPhysicalOperator_iff_mem_centralizer`),
   and their expectation values are the same at every vector of a gauge
   equivalence class (`expectation_physical_gauge_invariant`) — even when no
   vector of the Hilbert space is gauge invariant
   (`no_gauge_invariant_unit_vector_of_free`).
4. **The book's own example** (`book.tex` 2281–2289) — the lattice translations
   `e_k ↦ e_{k+1}` on `ℓ²(ℤ)` — is carried by the companion module
   `BookProof.ChapterGaugeShiftExample`, which is kept independent of this one so
   that the two threads of the development stay separately compilable.

A by-product recorded here: the auxiliary predicate
`ChapterG.IsUnconstrainedGaugeFixing` is unsatisfiable as stated
(`chapterG_isUnconstrainedGaugeFixing_vacuous`), which is why the notion is
re-formalized in this module as a property of the action on the spectrum rather
than of the invariant algebra.  This is a defect of that one predicate only: the
book's *definition* of an unconstrained gauge-fixing is satisfiable, and is
formalized, satisfied and shown to leave the full spectrum unconstrained in
`BookProof.ChapterGaugeUnconstrainedSpectrum`.

Everything is `sorry`-free.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterGaugeIncompleteFixing

/-! ## 1. The spectrum layer: comprehensive, complete, unconstrained -/

section Spectrum

variable {X : Type*}

/-- A gauge fixing `S` (a subset of the spectrum of the commutative algebra) is
**comprehensive** when it crosses *at least* once every gauge equivalence class
(`book.tex` 7406/7427). -/
def IsComprehensiveGaugeFixing (G : Type*) [Group G] [MulAction G X] (S : Set X) :
    Prop :=
  ∀ x : X, ∃ s ∈ S, ∃ g : G, g • s = x

/-- A gauge fixing `S` is **complete** when it crosses *at most* once each gauge
equivalence class, i.e. when there is no remnant gauge symmetry inside `S`
(`book.tex` 2294). -/
def IsCompleteGaugeFixing' (G : Type*) [Group G] [MulAction G X] (S : Set X) :
    Prop :=
  ∀ s ∈ S, ∀ t ∈ S, ∀ g : G, g • s = t → s = t

/-- The book's **unconstrained** condition, as a property of the action on the
spectrum: *"any non-trivial gauge transformation necessarily modifies any point
of the spectrum"* (`book.tex` 2336). It is exactly what forces the gauge
generators out of the commutative algebra. -/
def MovesEveryPointOfSpectrum (G : Type*) [Group G] (X : Type*) [MulAction G X] :
    Prop :=
  ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x

/-- A **physical observable**: an element of the commutative algebra that is
gauge invariant, i.e. constant on the gauge equivalence classes. -/
def IsPhysicalObservable (G : Type*) [Group G] [MulAction G X] (f : X → ℝ) : Prop :=
  ∀ (g : G) (x : X), f (g • x) = f x

variable (G : Type*) [Group G] [MulAction G X]









/-! ### The physical (gauge-invariant) algebra -/

/-- The gauge-invariant observables form a subalgebra of the commutative algebra
of all observables — the *physical* algebra. -/
noncomputable def physicalSubalgebra : Subalgebra ℝ (X → ℝ) where
  carrier := {f | IsPhysicalObservable G f}
  mul_mem' hf hg g x := by simp only [Pi.mul_apply, hf g x, hg g x]
  add_mem' hf hg g x := by simp only [Pi.add_apply, hf g x, hg g x]
  algebraMap_mem' _ _ _ := rfl











end Spectrum

/-! ## 2. The Hilbert-space layer: physical operators versus state vectors -/

section Hilbert

variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A family `U` of gauge unitaries on the Hilbert space. -/
def IsGaugeUnitaryFamily (U : G → (H →L[ℂ] H)) : Prop :=
  ∀ g : G, U g ∈ unitary (H →L[ℂ] H)

/-- A **physical operator** is one that commutes with every gauge unitary — the
book's *"operator of the commutative algebra which commutes with the gauge
generators"* (`book.tex` 2344). -/
def IsPhysicalOperator (U : G → (H →L[ℂ] H)) (A : H →L[ℂ] H) : Prop :=
  ∀ g : G, A * U g = U g * A







end Hilbert

/-! ## 3. A correction to an earlier predicate

`ChapterG.IsUnconstrainedGaugeFixing π` asks for a *gauge-invariant* function `f`
and a gauge transformation `g` with `f ∘ g ≠ f`, which contradicts invariance of
`f`: that predicate is unsatisfiable, so every statement conditioned on it is
vacuous. This says nothing against the book's definition, which is satisfiable:
the unconstrained condition of the book is the exclusion of the gauge generators
from the commutative algebra — so that they impose no constraint on the full
spectrum labelled by the basis vectors — formalized in
`BookProof.ChapterGaugeUnconstrainedSpectrum`, and equivalently rendered here as
the condition `MovesEveryPointOfSpectrum` on the action on the spectrum. -/



end BookProof.ChapterGaugeIncompleteFixing


