-- Prove2me | Definitions.Def_ChapterGaugeUnconstrainedSpectrum
-- name    : ChapterGaugeUnconstrainedSpectrum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:04:36.742263+00:00
-- url     : https://prove2.me/theorems/9963f3c5-99ce-4411-83f1-46a452031323
-- title:
--   Chapter GaugeUnconstrainedSpectrum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeUnconstrainedSpectrum.lean`): generated def bundle for ChapterGaugeUnconstrainedSpectrum. See BookProof/ChapterGaugeUnconstrainedSpectrum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeUnconstrainedSpectrum.lean

import Mathlib


/-!
# Unconstrained gauge-fixing: the book's definition, and why it *is* satisfiable

`book.tex` (line ~2296) defines:

> "We define gauge-fixing as unconstrained whenever the gauge generators are
> necessarily excluded from the commutative von Neumann algebra and thus do not
> impose constraints on the spectrum of the commutative algebra."

and later (line ~2356):

> "since bounded commuting normal operators can always be simultaneously
> diagonalized there is always one basis where the gauge unitary transformations
> are a function of the spectrum and (if the gauge-fixing is unconstrained) there
> is another basis where the gauge unitary transformations are not a function of
> the spectrum and thus there are no constraints."

The point of this module is that this definition is **satisfiable**, and that it
is satisfied by the book's own example.  The *spectrum* that the definition talks
about is the full spectrum labelled by the basis vectors `{e_x}` of the chosen
basis — **not** a subset carved out by the gauge generators.  A constraint on the
spectrum is a condition of the form "this element of the commutative algebra
takes the value `1` at the point `x` of the spectrum": only an operator that is a
*function of the spectrum* (i.e. a member of the commutative algebra, diagonal in
the basis) can impose such a condition.  When the gauge unitaries permute the
basis vectors non-trivially they are not diagonal, hence not members of the
commutative algebra, hence they impose no condition at all and the constrained
spectrum is the whole spectrum.

## The model

The commutative von Neumann algebra is presented in its Gelfand picture: the
spectrum is an index type `X`, the algebra is the algebra of functions `X → ℂ`
acting as the diagonal operators `diagOp d : f ↦ (x ↦ d x * f x)`, and the basis
vectors are the point masses `basisVec y`.  A gauge transformation which permutes
the basis, `e_y ↦ e_{σ y}`, is the operator `permOp σ`.

## What is proved

* `diagOp_mul_comm` — the algebra of the gauge-fixing is commutative, as the book
  insists.
* `permOp_isFunctionOfSpectrum_iff` — a basis permutation is a function of the
  spectrum **iff** it is trivial: every non-trivial gauge transformation is
  *necessarily excluded* from the commutative algebra.  This is exactly the
  book's clause "the gauge generators are necessarily excluded".
* `IsUnconstrainedGaugeFixing` — the book's definition, as a property of the
  family of gauge unitaries: no non-trivial gauge unitary is a function of the
  spectrum.
* `isUnconstrained_of_faithful`, `isUnconstrained_of_movesEveryPoint` — the
  definition **is satisfied** by every faithful permutation representation of the
  gauge group on the basis, in particular whenever every non-trivial gauge
  transformation moves every point of the spectrum.
* `shift_isUnconstrainedGaugeFixing`, `exists_isUnconstrainedGaugeFixing` — the
  book's own example `e_k ↦ e_{k+1}` on the basis indexed by `ℤ` is an
  unconstrained gauge-fixing; in particular the notion is **not vacuous**.
* `constrainedSpectrum_eq_univ_of_isUnconstrained` — and then the constrained
  spectrum is the *full* spectrum: the gauge generators impose no constraint on
  it.
* `signRep_isNotUnconstrained`, `signRep_constrainedSpectrum` — the
  contrast of the book's two-basis discussion: in a basis where the gauge
  unitaries *are* functions of the spectrum the very same gauge group does impose
  a constraint, cutting the spectrum down to a proper subset.

* `isPhysicalFunction_iff_factors`, `shift_observableSpectrum_subsingleton`,
  `shift_full_spectrum_vs_observable_spectrum` — the two spectra are *not* the
  same: the spectrum of the commutative subalgebra of gauge-invariant
  (observable) functions is the orbit space, a single point in the book's
  example, while the spectrum of the definition — the full spectrum labelled by
  the basis vectors — is all of `ℤ` and is left entirely unconstrained.

Everything is `sorry`-free.
-/

namespace BookProof.ChapterGaugeUnconstrainedSpectrum

variable {X : Type*}

/-! ## 1. The commutative algebra, its spectrum and its basis -/

/-- Operators in the chosen basis: linear maps of the space of coefficient
functions of the basis `{e_x}_{x ∈ X}`. -/
abbrev Op (X : Type*) := (X → ℂ) →ₗ[ℂ] (X → ℂ)

/-- The element of the commutative algebra given by the function `d` of the
spectrum: the operator diagonal in the basis, `e_x ↦ d x • e_x`.  These are the
*functions of the spectrum*. -/
def diagOp (d : X → ℂ) : Op X where
  toFun f := fun x => d x * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp [mul_left_comm]

/-- The gauge transformation permuting the basis vectors, `e_y ↦ e_{σ y}`. -/
def permOp (σ : Equiv.Perm X) : Op X where
  toFun f := fun x => f (σ.symm x)
  map_add' f g := by funext x; simp
  map_smul' c f := by funext x; simp

/-- The basis vector `e_y`, i.e. the point mass at the point `y` of the
spectrum. -/
def basisVec [DecidableEq X] (y : X) : X → ℂ := fun x => if x = y then 1 else 0

/-- An operator **is a function of the spectrum** when it belongs to the
commutative von Neumann algebra of the gauge-fixing, i.e. when it is diagonal in
the basis. -/
def IsFunctionOfSpectrum (T : Op X) : Prop := ∃ d : X → ℂ, T = diagOp d

















/-! ## 2. The book's definition of an unconstrained gauge-fixing -/

variable {G : Type*} [Group G]

/-- **The book's definition** (`book.tex` ~2296): a gauge-fixing — a commutative
von Neumann algebra, here the diagonal operators of a basis, together with the
family `U` of gauge unitaries — is *unconstrained* when the gauge generators are
necessarily excluded from the commutative algebra, i.e. when no non-trivial gauge
unitary is a function of the spectrum. -/
def IsUnconstrainedGaugeFixing (U : G → Op X) : Prop :=
  ∀ g : G, g ≠ 1 → ¬ IsFunctionOfSpectrum (U g)

/-- The **constrained spectrum**: the points of the full spectrum that survive
the constraints "the gauge unitary equals the identity" *as conditions on the
spectrum*.  Only a gauge unitary that is a function of the spectrum, `U g =
diagOp d`, produces such a condition, namely `d x = 1`. -/
def constrainedSpectrum (U : G → Op X) : Set X :=
  {x : X | ∀ (g : G) (d : X → ℂ), U g = diagOp d → d x = 1}







/-! ## 3. The book's own example: the lattice translations `e_k ↦ e_{k+1}` -/

/-- The translation representation of `ℤ` on the basis `{e_k}_{k ∈ ℤ}`:
`e_k ↦ e_{k+m}` (`book.tex` 2281–2289). -/
def shiftPerm : Multiplicative ℤ →* Equiv.Perm ℤ where
  toFun m := Equiv.addRight (Multiplicative.toAdd m)
  map_one' := by ext k; simp
  map_mul' m n := by
    ext k
    simp [Equiv.addRight, add_comm, add_left_comm]









/-! ## 4. The contrast: a *constrained* gauge-fixing

The book's two-basis discussion (`book.tex` ~2356): in a basis where the gauge
unitaries *are* functions of the spectrum, the same gauge group does impose
constraints, and the constrained spectrum is a proper subset of the full
spectrum.  Here is the sign representation of `ℤ`, diagonal in the basis, whose
constrained spectrum is the single point `0`. -/

/-- A gauge representation which *is* diagonal in the basis: `U m` multiplies the
basis vector `e_k` by `1` for `k = 0` and by `(-1)^m` otherwise. -/
noncomputable def signRep (m : Multiplicative ℤ) : Op ℤ :=
  diagOp fun k => if k = 0 then 1 else (-1 : ℂ) ^ (Multiplicative.toAdd m)





/-! ## 5. The two spectra: the full spectrum of the basis, and the spectrum of the
observables

The definition speaks of "the spectrum of the commutative algebra" used in the
gauge-fixing — the *full* spectrum, labelled by the basis vectors `{e_x}_{x ∈ X}`
— and **not** of the spectrum of the commutative subalgebra of gauge-invariant
(physical) observables, which is the orbit space `X/G`.  The two are genuinely
different, and it is the first one on which the gauge generators impose no
constraint.  In the book's own example they are as different as can be: the full
spectrum is all of `ℤ`, the spectrum of the observables is a single point. -/

/-- A function of the spectrum is a **physical observable** when it is gauge
invariant, i.e. constant on the gauge orbits. -/
def IsPhysicalFunction (ρ : G →* Equiv.Perm X) (d : X → ℂ) : Prop :=
  ∀ (g : G) (x : X), d (ρ g x) = d x

/-- The orbit equivalence of the gauge action on the full spectrum. -/
def orbitSetoid (ρ : G →* Equiv.Perm X) : Setoid X where
  r x y := ∃ g : G, ρ g x = y
  iseqv :=
    { refl := fun x => ⟨1, by simp⟩
      symm := by
        rintro x y ⟨g, rfl⟩
        exact ⟨g⁻¹, by rw [map_inv]; simp⟩
      trans := by
        rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨h * g, by rw [map_mul]; rfl⟩ }

/-- **The spectrum of the commutative subalgebra of observables**: the orbit
space `X/G` of the gauge action on the full spectrum. -/
def observableSpectrum (ρ : G →* Equiv.Perm X) : Type _ := Quotient (orbitSetoid ρ)









end BookProof.ChapterGaugeUnconstrainedSpectrum


