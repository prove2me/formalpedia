-- Prove2me | Definitions.Def_ChapterSecondQuantizationCoreEsa
-- name    : ChapterSecondQuantizationCoreEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-07T15:34:41.90567+00:00
-- url     : https://prove2.me/theorems/2f54c815-b766-41e5-8725-f21e1676d946
-- title:
--   The Lean 4 theorem `fockSectorCore_le_fockSectorDom` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSecondQuantizationCoreEsa.lean`): generated def bundle for ChapterSecondQuantizationCoreEsa. See BookProof/ChapterSecondQuantizationCoreEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSecondQuantizationCoreEsa.lean

import Theorems.Thm_BookProof_GraphCore_pushDom_mono

import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom

import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib


/-!
# Second quantization over an essentially self-adjoint one-particle operator

This module assembles the two instruments of the *core transfer* route into the second
quantization theorem for a one-particle operator `A` that is only **essentially** self-adjoint
on the one-particle core `D`:

1. the **core transfer principle** of `BookProof/ChapterGraphCoreTransfer.lean`: essential
   self-adjointness passes from a domain to any graph-norm dense subspace of it;
2. the **multilinear core estimate** of `BookProof/ChapterTensorGraphCore.lean`: if `D` is a
   core for `A`, then `D^{⊗n}` is a core for the sector derivation `dΓ(A)⁽ⁿ⁾` on `D₂^{⊗n}`;
3. the ℓ²-**direct sum** instrument `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn`,
   already in the tree: fibrewise essential self-adjointness glues along the particle-number
   decomposition.

The Fock space is the ℓ²-direct sum of the completed sectors
`𝓕ₙ = completion of H^{⊗n}`, and the finite-particle domain over the core is the algebraic
direct sum of the images of `D^{⊗n}` — `dsCore` applied to the sector cores.  This is the
domain `𝓕_fin(D)` of the statement.

The one hypothesis carried, sector by sector, is essential self-adjointness of `dΓ(A)⁽ⁿ⁾` on
the *full* tensor power `D₂^{⊗n}` of the domain of the closure — the statement for a
self-adjoint one-particle operator, whose proof (Nelson's analytic-vector or invariant-domain
argument) is a separate matter and is **not** proved here.  What is proved here is exactly the
step the essentially-self-adjoint hypothesis obstructs: the passage from the domain `D₂` of
the closure to the small core `D`, on every sector and then on the whole Fock space.

## Contents

* `fockSector` — the `n`-particle sector, the completion of `H^{⊗n}`;
* `fockSectorDom`, `fockSectorCore`, `fockSectorOp` — the sector domain `D₂^{⊗n}`, the sector
  core `D^{⊗n}` and the sector derivation inside it;
* `essentiallySelfAdjointOn_fockSectorCore` — sectorwise core transfer;
* `dGamma_essentiallySelfAdjointOn_fockCore` — **the main theorem**: `dΓ(A)` is essentially
  self-adjoint on the finite-particle domain over the core `D`.

Nothing is assumed beyond the stated sector hypothesis: the module contains no `axiom` and no
`sorry`.
-/

namespace BookProof.SecondQuantizationCore

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

/-- The `n`-particle sector of the Fock space: the Hilbert space completion of the algebraic
tensor power `H^{⊗n}`. -/
abbrev fockSector (n : ℕ) : Type := UniformSpace.Completion ((Hs.pow n).carrier)

/-- The isometric embedding of the algebraic tensor power into its completion. -/
def sectorEmb (n : ℕ) : (Hs.pow n).carrier →ₗᵢ[ℂ] fockSector Hs n :=
  UniformSpace.Completion.toComplₗᵢ

/-- The domain of the sector derivation inside the `n`-particle sector: the image of
`D₂^{⊗n}`. -/
def fockSectorDom (n : ℕ) : Submodule ℂ (fockSector Hs n) :=
  pushDom (sectorEmb Hs n) (sectorDom Hs D₂ n)

/-- The finite-particle core inside the `n`-particle sector: the image of `D^{⊗n}`. -/
def fockSectorCore (n : ℕ) : Submodule ℂ (fockSector Hs n) :=
  pushDom (sectorEmb Hs n) (sectorCore Hs D₂ D n)

/-- The sector derivation `dΓ(A)⁽ⁿ⁾` inside the `n`-particle sector. -/
def fockSectorOp (n : ℕ) : fockSectorDom Hs D₂ n →ₗ[ℂ] fockSector Hs n :=
  pushOp (sectorEmb Hs n) (sectorOp Hs D₂ A n)

theorem fockSectorCore_le_fockSectorDom (n : ℕ) :
    fockSectorCore Hs D₂ D n ≤ fockSectorDom Hs D₂ n :=
  pushDom_mono _ (sectorCore_le_sectorDom Hs D₂ D n)







/-- **The second quantization `dΓ(A)` on the finite-particle domain over the core `D`.** -/
def dGammaCoreOp :
    dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n) →ₗ[ℂ] lp (fun n : ℕ => fockSector Hs n) 2 :=
  dsOp (fun n : ℕ =>
    restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n))





/-! ## Non-vacuity -/



end

end BookProof.SecondQuantizationCore


