-- Prove2me | Definitions.Def_ChapterTwoParticleSectorEsa
-- name    : ChapterTwoParticleSectorEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T14:47:13.493038+00:00
-- url     : https://prove2.me/theorems/235f68cc-9b34-496d-aec8-8dbb823c5657
-- title:
--   Chapter TwoParticleSectorEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTwoParticleSectorEsa.lean`): generated def bundle for ChapterTwoParticleSectorEsa. See BookProof/ChapterTwoParticleSectorEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTwoParticleSectorEsa.lean

import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The bosonic and the fermionic two-particle sector

`BookProof.TensorCore` builds the sector derivation `dΓ(A)⁽ⁿ⁾` on the **full** tensor power
`H^{⊗n}` and proves that a one-particle core lifts to a core of it.  The physical two-particle
spaces are the *symmetric* and the *antisymmetric* halves of `H^{⊗2}`, i.e. the two
eigenspaces of the swap `x ⊗ y ↦ y ⊗ x`.  This module carries essential self-adjointness from
the full power to those halves.

The mechanism is the general reduction principle of `BookProof.ReducedEsa`: the swap is a
self-inverse isometry, it preserves the domain `D₂^{⊗2}` and the core `D^{⊗2}`, and it
commutes with the derivation — the Leibniz rule is symmetric in the two factors.  Hence the
projections `(1 ± swap)/2` are reducing projections for the derivation, and essential
self-adjointness descends to each sector.

## Contents

* `swapTwo` — the swap of a two-fold (nested) tensor power `X ⊗ (X ⊗ ℂ)`, as a linear
  isometry equivalence; `swapTwo_tmul`, `swapTwo_involutive`, `swapTwo_inner`.
* `swapH`, `swapDom` — the swap on `H^{⊗2}` and on `D₂^{⊗2}`, and their compatibility with
  the inclusion (`inclPow_swapDom`) and with the derivation (`derPow_swapDom`).
* `swapH_mem_sectorDom`, `swapH_mem_sectorCore` — the swap preserves the domain and the core.
* `sectorOp_swapH`, `restrictOp_sectorOp_swapH` — the swap commutes with the two-particle
  derivation, on the domain and on the core.
* **`essentiallySelfAdjointOn_bosonic`**, **`essentiallySelfAdjointOn_fermionic`** — the two
  sector statements on the domain `D₂^{⊗2}`; **`essentiallySelfAdjointOn_bosonic_core`**,
  **`essentiallySelfAdjointOn_fermionic_core`** — the same on the symmetrized and the
  antisymmetrized one-particle core `D^{⊗2}`, for any core `D` of `A`.
* `mem_bosonic_iff`, `mem_fermionic_iff` — the two sectors are exactly the `+1` and the `-1`
  eigenspaces of the swap.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TwoParticleSector

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

/-! ## The swap of a two-fold tensor power -/

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The **swap** `x ⊗ (y ⊗ c) ↦ y ⊗ (x ⊗ c)` of a two-fold tensor power, in the nested form
`X ⊗ (X ⊗ ℂ)` in which `BookProof.TensorCore.IPSpace.pow` presents `X^{⊗2}`.  It is built
from the associator and the commutor, so it is an isometry. -/
def swapTwo : X ⊗[ℂ] (X ⊗[ℂ] ℂ) ≃ₗᵢ[ℂ] X ⊗[ℂ] (X ⊗[ℂ] ℂ) :=
  (TensorProduct.assocIsometry ℂ X X ℂ).symm.trans
    ((TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ X X)
      (LinearIsometryEquiv.refl ℂ ℂ)).trans (TensorProduct.assocIsometry ℂ X X ℂ))

@[simp] theorem swapTwo_tmul (x y : X) (c : ℂ) :
    swapTwo X (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] c)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] c) := by
  simp [swapTwo, TensorProduct.congrIsometry]

variable {X}





/-! ## The swap on the two-particle space and on its domain -/

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)

/-- The swap of `H^{⊗2}`, as a linear map. -/
def swapH : (Hs.pow 2).carrier →ₗ[ℂ] (Hs.pow 2).carrier :=
  (swapTwo (X := Hs.carrier)).toLinearEquiv.toLinearMap

/-- The swap of the algebraic tensor square `D₂^{⊗2}` of the domain. -/
def swapDom : ((domSpace Hs D₂).pow 2).carrier →ₗ[ℂ] ((domSpace Hs D₂).pow 2).carrier :=
  (swapTwo (X := D₂)).toLinearEquiv.toLinearMap

@[simp] theorem swapH_tmul (x y : Hs.carrier) (c : ℂ) :
    swapH Hs (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] c) : (Hs.pow 2).carrier) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] c) :=
  swapTwo_tmul Hs.carrier x y c

@[simp] theorem swapDom_tmul (a b : D₂) (c : ℂ) :
    swapDom Hs D₂ (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
      = b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c) :=
  swapTwo_tmul (D₂ : Type) a b c









variable (A : D₂ →ₗ[ℂ] Hs.carrier)





/-! ## The swap preserves the domain and the core -/



variable (D : Submodule ℂ Hs.carrier)





/-! ## The swap commutes with the two-particle operator -/





/-! ## The two sectors -/

/-- The bosonic (symmetric) two-particle sector: the range of `(1 + swap)/2`. -/
def bosonicProj : (Hs.pow 2).carrier →ₗ[ℂ] (Hs.pow 2).carrier := symProj (swapH Hs)

/-- The fermionic (antisymmetric) two-particle sector: the range of `(1 - swap)/2`. -/
def fermionicProj : (Hs.pow 2).carrier →ₗ[ℂ] (Hs.pow 2).carrier := asymProj (swapH Hs)









/-! ## Essential self-adjointness on the two sectors -/









/-! ## Non-vacuity of the two sectors -/





/-! ## Symmetry of the sector operators -/





end

end BookProof.TwoParticleSector


