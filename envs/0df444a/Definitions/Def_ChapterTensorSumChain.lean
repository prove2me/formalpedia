-- Prove2me | Definitions.Def_ChapterTensorSumChain
-- name    : ChapterTensorSumChain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T14:55:13.070106+00:00
-- url     : https://prove2.me/theorems/24ea6c9e-c056-4bc7-afd8-0878221de85a
-- title:
--   Chapter TensorSumChain
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorSumChain.lean`): generated def bundle for ChapterTensorSumChain. See BookProof/ChapterTensorSumChain.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorSumChain.lean

import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric

import Definitions.Def_ChapterTensorSumEsa
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterEsaOneParticleDGamma
import Mathlib


/-!
# Finitely many factors: the total tensor sum `∑ᵢ 1 ⊗ ⋯ ⊗ Aᵢ ⊗ ⋯ ⊗ 1`

`BookProof/ChapterTensorSumEsa.lean` proves the two-factor statement: for symmetric,
essentially self-adjoint `A` on `H` and `B` on `K`, the tensor sum `A ⊗ 1 + 1 ⊗ B` is
essentially self-adjoint on the algebraic tensor product of the two domains inside `H ⊗̂ K`.
Crucially the *conclusion* is of the same shape as the two *hypotheses* — symmetric,
essentially self-adjoint, densely defined on a Hilbert space — so the statement iterates.

This module performs the iteration.  `EsaOp` bundles exactly the data the two-factor theorem
consumes and produces (a Hilbert space, a dense domain, a symmetric operator on it, and
essential self-adjointness), `pair` is the two-factor theorem in that vocabulary, and `chain`
folds `pair` along a list.  The result is the total tensor sum of an arbitrary finite family
of *different* operators on *different* Hilbert spaces:

`H = A₁ ⊗ 1 ⊗ ⋯ ⊗ 1 + 1 ⊗ A₂ ⊗ 1 ⊗ ⋯ ⊗ 1 + ⋯ + 1 ⊗ ⋯ ⊗ 1 ⊗ A_n`,

the Hamiltonian of `n` non-interacting degrees of freedom, essentially self-adjoint on the
algebraic tensor product of the `n` domains, with a complete unitary flow.

## Contents

* `EsaOp` — the bundle; `pair` — the two-factor step; `pair_op_tmul` — the operator really is
  `(x ⊗ y) ↦ A x ⊗ y + x ⊗ B y`.
* `chain`, `chain_dense`, `chain_symmetric`, **`chain_esa`** — the `n`-factor tensor sum is
  densely defined, symmetric and essentially self-adjoint; `chain_stone_flow` — its unitary
  group.
* `chain_singleton`, `chain_cons` — the two recursion equations.
* `posEsaOp`, `positionChain_esa` — the concrete instance: `n` copies of the (unbounded)
  position operator of `ℓ²(ℤ)`, whose total tensor sum `k₁ + k₂ + ⋯ + kₙ` is essentially
  self-adjoint.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorSumChain

open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumEsa
  BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.GraphCore
  BookProof.EsaClosure

noncomputable section

/-- A symmetric operator, essentially self-adjoint on a dense domain of a Hilbert space:
exactly the data the two-factor tensor-sum theorem consumes, and exactly what it produces. -/
structure EsaOp where
  /-- the Hilbert space -/
  space : IPSpace
  /-- it is complete -/
  complete : CompleteSpace space.carrier
  /-- the domain -/
  dom : Submodule ℂ space.carrier
  /-- the operator -/
  op : dom →ₗ[ℂ] space.carrier
  /-- the domain is dense -/
  dense : Dense (dom : Set space.carrier)
  /-- the operator is symmetric -/
  sym : SymmetricOn dom op
  /-- and essentially self-adjoint -/
  esa : EssentiallySelfAdjointOn dom op

/-- **The two-factor step.**  The tensor sum `A ⊗ 1 + 1 ⊗ B` of two members of the class is
again a member of the class, on the completed tensor product of the two spaces. -/
def pair (E F : EsaOp) : EsaOp :=
  haveI := E.complete
  haveI := F.complete
  { space := ⟨ctensor E.space F.space⟩
    complete := inferInstanceAs (CompleteSpace (ctensor E.space F.space))
    dom := cpairDom E.space F.space E.dom F.dom
    op := cpairOp E.space F.space E.dom F.dom E.op F.op
    dense := dense_cpairDom E.space F.space E.dom F.dom E.dense F.dense
    sym := symmetricOn_cpairOp E.space F.space E.dom F.dom E.op F.op E.sym F.sym
    esa := essentiallySelfAdjointOn_cpairDom_esa E.op F.op E.dense F.dense E.sym F.sym
      E.esa F.esa }

@[simp] theorem pair_space (E F : EsaOp) :
    (pair E F).space = ⟨ctensor E.space F.space⟩ := rfl

@[simp] theorem pair_dom (E F : EsaOp) :
    (pair E F).dom = cpairDom E.space F.space E.dom F.dom := rfl



/-- The total tensor sum of a nonempty finite family, by folding the two-factor step. -/
def chain : EsaOp → List EsaOp → EsaOp
  | E, [] => E
  | E, (F :: rest) => pair E (chain F rest)

@[simp] theorem chain_singleton (E : EsaOp) : chain E [] = E := rfl

@[simp] theorem chain_cons (E F : EsaOp) (L : List EsaOp) :
    chain E (F :: L) = pair E (chain F L) := rfl









/-! ## A genuinely unbounded instance: `n` copies of the position operator -/

section Position

open BookProof.ChapterStoneSeparable BookProof.ChapterUnboundedPosition
  BookProof.FlowDGamma BookProof.EsaOneParticle

/-- The position operator of `ℓ²(ℤ)` as a member of the class. -/
def posEsaOp : EsaOp where
  space := L2ZSpace
  complete := inferInstanceAs (CompleteSpace L2ZSpace.carrier)
  dom := (mulSA positionField).domain
  op := (mulSA positionField).op
  dense := (mulSA positionField).denseDomain
  sym := (mulSA positionField).symmetric
  esa := essentiallySelfAdjointOn_of_selfAdjoint (Hs := L2ZSpace) (mulSA positionField)





end Position

end

end BookProof.TensorSumChain


