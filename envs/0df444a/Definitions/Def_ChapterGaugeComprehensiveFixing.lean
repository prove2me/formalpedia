-- Prove2me | Definitions.Def_ChapterGaugeComprehensiveFixing
-- name    : ChapterGaugeComprehensiveFixing
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:01:07.53099+00:00
-- url     : https://prove2.me/theorems/cf00d5a4-d4bf-4da3-8fcb-33b3fbb1c4ed
-- title:
--   Chapter GaugeComprehensiveFixing
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeComprehensiveFixing.lean`): generated def bundle for ChapterGaugeComprehensiveFixing. See BookProof/ChapterGaugeComprehensiveFixing.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeComprehensiveFixing.lean

import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib


/-!
# Comprehensive gauge fixings: existence, uniqueness of the extension, and the
Gribov obstruction

This module continues the formalization of the section *"Gauge transformations,
constrained systems and conditioned probability"* of `book.tex` (lines 2221–2400).
The companion module `BookProof.ChapterGaugeIncompleteFixing` sets up the book's
vocabulary — a gauge fixing is a subset `S` of the spectrum of the commutative von
Neumann algebra, it is *comprehensive* when it crosses at least once each gauge
equivalence class, *complete* when it crosses at most once each class, and
*unconstrained* when every non-trivial gauge transformation moves every point of
the spectrum — and proves that a comprehensive gauge fixing loses no physical
information.  What is added here is the *existence* theory and the obstruction the
book attributes to the Gribov ambiguity:

> "The Dirac brackets require the gauge-fixing to be both unconstrained and
> complete (as if the gauge symmetry could be eliminated), which is not possible
> in general due to the Gribov ambiguity." (`book.tex` 2301–2304)

## Results

* `orbitRepresentatives_isComprehensiveGaugeFixing`,
  `orbitRepresentatives_isCompleteGaugeFixing'`,
  `exists_comprehensive_complete_gaugeFixing` — a gauge fixing which is
  simultaneously comprehensive and complete always exists *as a set*: the set of
  representatives of the gauge equivalence classes.  So the obstruction below is
  not a set-theoretic one.
* `existsUnique_mem_of_complete_comprehensive` — on such a gauge fixing each point
  of the spectrum has exactly one gauge representative, and
  `exists_physical_extension_of_complete`,
  `existsUnique_physical_extension_of_complete` — *every* function on it is the
  restriction of exactly one gauge-invariant (physical) observable: a complete
  comprehensive gauge fixing is a faithful parametrization of the physical
  algebra.
* `not_isPhysicalObservable_indicator` — nevertheless the gauge-fixing condition
  itself is never a physical observable when the gauge group acts freely: the
  gauge fixing is extra data, not an observable.
* `not_isClopen_of_complete_comprehensive` — **the obstruction.**  If the spectrum
  is connected and the gauge group acts freely and non-trivially, a complete
  comprehensive gauge fixing is never clopen, i.e. it can never be cut out by a
  locally constant (continuous) gauge condition.  Completeness can be achieved
  only by a discontinuous choice.
* The book's simplest concrete instance, `ℤ` acting on the line by translations
  (`shiftAction`): the unit cell `[0,1)` is a complete comprehensive gauge fixing
  (`unitCell_isComprehensiveGaugeFixing`, `unitCell_isCompleteGaugeFixing'`),
  the action is unconstrained in the book's sense
  (`shift_movesEveryPointOfSpectrum`), and no complete comprehensive gauge fixing
  of this action is clopen (`shift_no_clopen_complete_gaugeFixing`) — an explicit
  Gribov-type ambiguity.
* `physical_ext_iff_comprehensive`, `physical_extension_iff_complete` — the two
  axes of the book's classification are **exactly** the two halves of the
  statement that restriction to the gauge-fixing surface is a bijection from the
  physical algebra onto the functions of the surface: comprehensiveness is
  injectivity (no physical information is lost), completeness is surjectivity (no
  remnant symmetry constrains the surface).
* `spuriousSection_isComprehensiveGaugeFixing`,
  `spuriousSection_isCompleteGaugeFixing'` — the manuscript's device of adjoining
  a *spurious* field with a constraint (`book.tex` 7406) does produce a gauge
  fixing that is at once complete and comprehensive, for an arbitrary gauge
  group: the spurious factor is a copy of the gauge group, fixed to the
  identity.
* `shift_gaugeFixing_classification` — all four combinations of the two axes
  occur, with explicit witnesses for the translation gauge symmetry of the line;
  the book uses a *complete non-comprehensive* fixing (the magnetic components in
  the Weyl gauge, `book.tex` 7427) as well as *complete and comprehensive* ones
  (`book.tex` 7406) and the incomplete unconstrained one of `book.tex` 2336.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterGaugeComprehensiveFixing

open BookProof.ChapterGaugeIncompleteFixing

/-! ## 1. Existence of a complete comprehensive gauge fixing -/

section Existence

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]

/-- A set of representatives of the gauge equivalence classes: one point of the
spectrum chosen in each class. -/
noncomputable def orbitRepresentatives : Set X :=
  Set.range fun c : Quotient (MulAction.orbitRel G X) => c.out







end Existence

/-! ## 2. A complete comprehensive gauge fixing parametrizes the physical algebra -/

section Complete

variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}









end Complete

/-! ## 3. The Gribov obstruction: completeness is incompatible with continuity -/

section Gribov

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G] [MulAction G X]



end Gribov

/-! ## 4. The two axes are injectivity and surjectivity of the restriction -/

section Classification

variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}









end Classification

/-! ## 5. The spurious field of `book.tex` 7406 -/

section Spurious

variable (X : Type*) (G : Type*) [Group G] [MulAction G X]

/-- The gauge fixing obtained by adjoining a *spurious* degree of freedom that
takes values in the gauge group itself and setting it to the identity — the
manuscript's "new field `Φ` and new constraint `Π = 0`" which "allows a complete
and comprehensive gauge-fixing" (`book.tex` 7406).  The gauge group acts
diagonally on `X × G`, by the original action on `X` and by left translation on
the spurious factor. -/
def spuriousSection : Set (X × G) := {p | p.2 = 1}





end Spurious

/-! ## 6. The book's concrete example: translations of the line -/

section Shift

/-- The gauge group `ℤ` (written multiplicatively) acting on the spectrum `ℝ` by
translations.  This is the continuous analogue of the book's lattice example
`e_k ↦ e_{k+1}` (`book.tex` 2281–2289). -/
scoped instance shiftAction : MulAction (Multiplicative ℤ) ℝ where
  smul n x := ((Multiplicative.toAdd n : ℤ) : ℝ) + x
  one_smul x := by
    change ((0 : ℤ) : ℝ) + x = x
    simp
  mul_smul m n x := by
    change ((Multiplicative.toAdd (m * n) : ℤ) : ℝ) + x
        = ((Multiplicative.toAdd m : ℤ) : ℝ) + (((Multiplicative.toAdd n : ℤ) : ℝ) + x)
    rw [show Multiplicative.toAdd (m * n)
        = Multiplicative.toAdd m + Multiplicative.toAdd n from rfl]
    push_cast
    ring



/-- The unit cell `[0, 1)`: the standard gauge fixing of the translation gauge
symmetry of the line. -/
def unitCell : Set ℝ := Set.Ico 0 1

















end Shift

end BookProof.ChapterGaugeComprehensiveFixing


