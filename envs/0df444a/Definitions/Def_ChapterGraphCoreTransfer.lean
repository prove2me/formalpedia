-- Prove2me | Definitions.Def_ChapterGraphCoreTransfer
-- name    : ChapterGraphCoreTransfer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:08:28.451982+00:00
-- url     : https://prove2.me/theorems/4a2a25d9-798b-4804-abbf-b7c319e75cb6
-- title:
--   Chapter GraphCoreTransfer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGraphCoreTransfer.lean`): generated def bundle for ChapterGraphCoreTransfer. See BookProof/ChapterGraphCoreTransfer.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGraphCoreTransfer.lean

import Definitions.Def_ChapterFarisLavineCore
import Mathlib


/-!
# The core transfer principle: graph-norm density transfers essential self-adjointness

Everywhere in this project essential self-adjointness of a symmetric operator
`T : D →ₗ[ℂ] F` is rendered by the vanishing of the deficiency spaces of the adjoint
(`BookProof.FarisLavine.EssentiallySelfAdjointOn`).  All the criteria available so far
(Faris–Lavine, Nelson-type commutator bounds, …) verify this on the domain on which the
operator is given.  The present module supplies the missing *domain-changing* instrument:

> **Core transfer.**  Let `T₂` be an operator on `D₂` and let `D₁ ≤ D₂` be a subspace which
> is dense in `D₂` for the **graph norm** `‖x‖ + ‖T₂ x‖` of `T₂`.  Then every deficiency
> space of the restriction `T₂|_{D₁}` is contained in the corresponding deficiency space of
> `T₂`; in particular, if `T₂` is essentially self-adjoint on `D₂`, then its restriction to
> `D₁` is essentially self-adjoint on `D₁`.

This is the standard way to handle an operator that is only *essentially* self-adjoint on a
small domain `D`: one never has to make `D` invariant under the unitary group, nor to invert
`A ± i` on `D`.  One works with the self-adjoint (or merely essentially self-adjoint)
operator on the larger domain and transfers the conclusion back along the graph-norm
density.

## Contents

* `IsGraphCore D₁ T` — `D₁` is a core for `T` (graph-norm dense in the domain of `T`).
* `restrictOp` — the restriction of an operator to a smaller domain; `restrictOp_apply`,
  `symmetricOn_restrictOp`.
* `IsGraphCore.refl`, `IsGraphCore.trans` — a domain is a core for its own operator, and
  cores compose.
* `deficiencyTrivialAt_of_graphCore` — the transfer of one deficiency space.
* `essentiallySelfAdjointOn_of_graphCore` — **the core transfer principle.**
* `isGraphCore_of_isometry` — the same notion transported along a linear isometry, which is
  how a core inside an incomplete space becomes a core inside its completion.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.GraphCore

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Restriction of an operator to a smaller domain -/

/-- The restriction of `T : D₂ →ₗ[ℂ] F` to a subspace `D₁ ≤ D₂`. -/
def restrictOp {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) : D₁ →ₗ[ℂ] F :=
  T ∘ₗ Submodule.inclusion h





/-! ## Cores -/

/-- `D₁` is a **core** for the operator `T` defined on `D₂`: every vector of `D₂` is
approximated, simultaneously in the norm and in the norm of its image under `T` — that is,
in the graph norm of `T` — by vectors of `D₁`.  (The inclusion `D₁ ≤ D₂` is part of the
statement: the approximating vectors are elements of `D₂` that lie in `D₁`.) -/
def IsGraphCore (D₁ : Submodule ℂ F) {D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) : Prop :=
  ∀ x : D₂, ∀ ε > 0, ∃ y : D₂, (y : F) ∈ D₁ ∧ ‖(x : F) - (y : F)‖ < ε ∧ ‖T x - T y‖ < ε





/-! ## The transfer -/





/-! ## A criterion: bounded and symmetric on a dense domain

The transfer principle consumes essential self-adjointness on the large domain.  The
following elementary criterion produces it in the bounded case, and is what makes the whole
package non-vacuous: for a densely defined *bounded* symmetric operator the expectation
`⟪T v, v⟫` is real, while the deficiency equation forces a purely imaginary value in the
limit `v → w`; hence `w = 0`. -/





/-! ## Transport along a linear isometry

A core stays a core when the ambient space is enlarged along a linear isometry — in
particular when an incomplete space is replaced by its completion, which is how the sectors
of a Fock space are built below. -/

section Transport

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The image of a domain under a linear isometry. -/
def pushDom (U : F →ₗᵢ[ℂ] G) (D : Submodule ℂ F) : Submodule ℂ G :=
  Submodule.map U.toLinearMap D





/-- An operator transported along a linear isometry: `U T U⁻¹` on the image domain. -/
noncomputable def pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) :
    pushDom U D →ₗ[ℂ] G :=
  (U.toLinearMap ∘ₗ T) ∘ₗ
    (Submodule.equivMapOfInjective U.toLinearMap U.injective D).symm.toLinearMap







end Transport

end BookProof.GraphCore


