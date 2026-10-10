-- Prove2me | Definitions.Def_ChapterSchurFiniteDim
-- name    : ChapterSchurFiniteDim
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:18:02.190722+00:00
-- url     : https://prove2.me/theorems/421b148c-3f62-42b5-80e3-656cc7929d30
-- title:
--   Chapter SchurFiniteDim
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSchurFiniteDim.lean`): generated def bundle for ChapterSchurFiniteDim. See BookProof/ChapterSchurFiniteDim.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchurFiniteDim.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA2
import Mathlib


/-!
# Schur's lemma in finite dimensions

`BookProof.ChapterA2` introduces the Schur property for unitaries
(`IsSchurUnitary`) as a *named hypothesis*, because the general
unitary-representation Schur lemma is not available in Mathlib.

This file discharges that hypothesis in the **finite-dimensional complex** case,
where it is a theorem rather than an external input:

* `schur_scalar_of_irreducible` — a linear endomorphism of a nonzero
  finite-dimensional complex space which commutes with an irreducible system of
  operators is a scalar;
* `isSchurUnitary_of_irreducible` — consequently, every irreducible system on a
  nonzero finite-dimensional complex inner-product space *is* Schur for
  unitaries, so `BookProof.ChapterA2`'s hypothesis holds automatically there.

The proof is the classical one: over `ℂ` the commuting operator has an
eigenvalue (algebraic closedness plus finite dimension), its eigenspace is
invariant under the system and nonzero, hence everything, so the operator is the
corresponding scalar.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Module

namespace BookProof.ChapterSchurFiniteDim

open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Irreducibility of a system.**  The only subspaces invariant under every
operator of the system are `⊥` and `⊤`. -/
def IsIrreducibleSystem (M : System ℂ V) : Prop :=
  ∀ W : Submodule ℂ V, (∀ m ∈ M.ops, ∀ x ∈ W, m x ∈ W) → W = ⊥ ∨ W = ⊤





end BookProof.ChapterSchurFiniteDim


