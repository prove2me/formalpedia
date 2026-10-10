-- Prove2me | Definitions.Def_ChapterSchurIrreducible
-- name    : ChapterSchurIrreducible
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:43:59.459993+00:00
-- url     : https://prove2.me/theorems/286d2612-da29-4d77-96f8-45d37cc5ebf0
-- title:
--   Chapter SchurIrreducible
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSchurIrreducible.lean`): generated def bundle for ChapterSchurIrreducible. See BookProof/ChapterSchurIrreducible.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchurIrreducible.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA2b
import Mathlib


/-!
# Schur's lemma for irreducible normal systems on an arbitrary complex Hilbert space

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §*Systems on real and complex Hilbert spaces* and §*Schur systems*
(Def 13, Lemma 28: "Schur's lemma for unitary representations").

`BookProof.ChapterA2b` introduces the **full Schur property**

```
IsSchurFull M : ∀ S : V →L[ℂ] V, M.Commutes S → ∃ c : ℂ, S = c • 1
```

and `BookProof.ChapterA2` the unitary variant `IsSchurUnitary`.  Both were introduced as
*named hypotheses*, because Schur's lemma for unitary representations on a possibly
infinite-dimensional Hilbert space is not available in Mathlib;
`BookProof.ChapterSchurFullFiniteDim` discharges them only in **finite** dimension, where
an eigenvalue exists.

This file discharges them in **full generality**: for a *normal* system (a set of bounded
operators closed under the adjoint — Def 24) which is *topologically irreducible*
(Def 7), every bounded operator commuting with the system is a complex scalar.  The proof
uses no eigenvalues; it uses only the **continuous functional calculus** of a bounded
self-adjoint operator:

* if a self-adjoint `T` in the commutant had two distinct spectral points `p < q`, then
  with `f x = max 0 (mid - x)`, `g x = max 0 (x - mid)` (`mid` the midpoint) the operators
  `F = f(T)`, `G = g(T)` are nonzero (their spectra are `f '' spectrum T ∋ f p ≠ 0`,
  resp. `g '' spectrum T ∋ g q ≠ 0`), satisfy `G * F = 0`, and lie in the commutant of
  everything commuting with `T`;
* hence the closure of the range of `F` is a **closed invariant subspace** which is
  nonzero (as `F ≠ 0`) and proper (it lies in `ker G ≠ ⊤`), contradicting irreducibility;
* so the spectrum of `T` is a single point `c` and the functional calculus gives
  `T = c • 1` directly (`cfc_congr` against the constant function);
* a general commuting operator splits as `S = A + i B` with `A = (S + S*)/2`,
  `B = (S - S*)/(2i)` self-adjoint; normality of the system makes `S*` commute with it
  too, so both parts are real scalars and `S` is a complex scalar.

## Main results

* `spectrum_subsingleton_of_irreducible` — the spectrum of a self-adjoint operator in the
  commutant of an irreducible system is a subsingleton.
* `selfAdjoint_commutant_scalar` — such an operator is a real scalar.
* `commutant_scalar_of_irreducible` — **Schur's lemma**: every bounded operator commuting
  with an irreducible normal system is a complex scalar.
* `isSchurFull_of_irreducible`, `isSchurUnitary_of_irreducible` — the two `EXTERNAL`
  hypotheses of `ChapterA2` / `ChapterA2b`, now *theorems*, with no dimension restriction.
* `commutant_eq_scalars_of_irreducible` — the commutant of an irreducible normal system is
  exactly `ℂ · 1`; `isNormal_and_irreducible_iff_schur` records the converse direction
  (the book's Lemma 27, `ChapterA.System.schur_normal_irreducible`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterSchurIrreducible

open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## The closure of a range as a closed invariant subspace -/

/-- The closure of the range of a bounded operator, as a closed subspace. -/
noncomputable def rangeClosure (F : V →L[ℂ] V) : Submodule ℂ V :=
  (LinearMap.range (F : V →ₗ[ℂ] V)).topologicalClosure













/-! ## The functional calculus of a commuting self-adjoint operator -/





/-! ## Schur's lemma -/













end BookProof.ChapterSchurIrreducible


