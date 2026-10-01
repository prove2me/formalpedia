-- Prove2me | Definitions.Def_ChapterAbelianAtomicCondensation
-- name    : ChapterAbelianAtomicCondensation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:23:43.380055+00:00
-- url     : https://prove2.me/theorems/215717c5-0301-49b5-9264-112ab2bff262
-- title:
--   Chapter AbelianAtomicCondensation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianAtomicCondensation.lean`): generated def bundle for ChapterAbelianAtomicCondensation. See BookProof/ChapterAbelianAtomicCondensation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianAtomicCondensation.lean

import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterAtomicDecomposition
import Mathlib


/-!
# The purely atomic condensation of the abelian von Neumann classification
(plan GAP-2)

`ChapterAbelianDiagonal` (type `Iₙ`), `ChapterAbelianDiagonalCountable`
(type `I∞`, `ℓ∞(ℕ)`), `ChapterLinftyMultiplication` (the diffuse class `L∞(μ)`) and
`ChapterAbelianMixture` (the mixed class) realize the four concrete classes of von
Neumann's list.  The *exhaustiveness* of the five-way list — every abelian von
Neumann algebra on a separable `L²` is `*`-isomorphic to one of them — is the full
von Neumann theorem and is out of reach of the current toolchain (Mathlib has no
von Neumann algebra classification, no bicommutant theorem for these algebras).

What this module proves is the **purely atomic condensation** the plan asks for:
in the purely atomic case the classification *is* provable, and it collapses to
`ℓ∞(ℕ)` (or, in the finite case, to `Iₙ`).

## Deliverables

* `atomProj i` — the minimal (rank-one, "atomic") projections of `ℓ²(ℕ)`;
* `commutes_atomProj_iff` — **the condensation step**: a bounded operator commutes
  with *every atomic projection* iff it is a diagonal multiplication operator.
  Only the atoms are needed; the whole diagonal algebra is not assumed;
* `IsAtomicAbelian` — an algebra of operators is *purely atomic abelian* when it
  contains every atomic projection and its elements commute pairwise;
* `atomic_abelian_subset_diagonal` — every such algebra consists of diagonal
  operators, so `diagOp` identifies it with a subalgebra of `ℓ∞(ℕ)`;
* `atomic_abelian_maximal_eq_diagonal` — **headline**: a purely atomic abelian
  algebra that is *maximal* abelian is exactly the diagonal algebra, i.e.
  `*`-isomorphic to `ℓ∞(ℕ)` via the unital `*`-map `diagOp`
  (`diagOp_injective`, `diagOp_add`, `diagOp_mul`, `diagOp_one`, `diagOp_star`);
* `atomic_measure_index_dichotomy` — the measure-theoretic side of the same
  condensation: a purely atomic probability measure has a countable atom set, so
  the index set is either `Fin n` (class `Iₙ`) or `ℕ` (class `ℓ∞(ℕ)`); there is no
  third purely atomic class.

## Documented obstruction (GAP-2, unchanged)

The step that remains beyond this condensation is the *diffuse* half: that an
abelian von Neumann algebra whose projections are not purely atomic contains a
copy of `L∞[0,1]`, and that the general algebra splits as an atomic part plus a
diffuse part.  In the measure-theoretic model that splitting *is* available
(`ChapterAtomicDecomposition.eq_continuousPart_add_atomicPart`,
`probability_measure_five_types`); what is missing is the passage from an abstract
von Neumann algebra to a measure model — the spectral/Gelfand step — for which
Mathlib currently has no `L∞(μ)`-valued spectral theorem for abelian von Neumann
algebras.  This is recorded as an obstruction, never as a `sorry`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ENNReal

noncomputable section

namespace BookProof.ChapterAbelianAtomicCondensation

open BookProof.ChapterAbelianDiagonalCountable

/-! ## The atomic projections and the condensation step -/

/-- The `i`-th **atomic projection** of `ℓ²(ℕ)`: the rank-one projection onto the
`i`-th coordinate axis, realized as a diagonal multiplication operator. -/
def atomProj (i : ℕ) : Ell2C →L[ℂ] Ell2C := diagOp (coordUnit i)







/-! ## Purely atomic abelian algebras -/

/-- An algebra of operators on `ℓ²(ℕ)` is **purely atomic abelian** when it
contains every atomic (minimal) projection and its elements commute pairwise.
This is the operator-algebraic form of "the projections of the algebra are purely
atomic". -/
structure IsAtomicAbelian (A : Set (Ell2C →L[ℂ] Ell2C)) : Prop where
  /-- Every atomic projection belongs to the algebra. -/
  atoms_mem : ∀ i : ℕ, atomProj i ∈ A
  /-- The algebra is abelian. -/
  abelian : ∀ S ∈ A, ∀ T ∈ A, S.comp T = T.comp S







/-! ## The measure-theoretic side: only two purely atomic classes -/

open MeasureTheory BookProof.ChapterAtomicDecomposition



end BookProof.ChapterAbelianAtomicCondensation

end


