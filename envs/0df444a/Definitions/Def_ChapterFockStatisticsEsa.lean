-- Prove2me | Definitions.Def_ChapterFockStatisticsEsa
-- name    : ChapterFockStatisticsEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-07T22:25:41.564968+00:00
-- url     : https://prove2.me/theorems/d9289112-bd48-4e17-a6a6-55c45b4c2267
-- title:
--   Chapter FockStatisticsEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockStatisticsEsa.lean`): generated def bundle for ChapterFockStatisticsEsa. See BookProof/ChapterFockStatisticsEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockStatisticsEsa.lean

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj

import Theorems.Thm_BookProof_PermSector_isReducingProjection_fermionicProj

import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom

import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom



import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj

import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom

import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom




import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorCore

import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore

import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom




import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorCore

import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorCore


import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorPermutation
import Mathlib


/-!
# The bosonic and the fermionic Fock space

`BookProof.PermSector` proves that the sector derivation `dΓ(A)⁽ⁿ⁾` is essentially
self-adjoint on the symmetric and on the antisymmetric part of `H^{⊗n}` **as soon as it is
essentially self-adjoint on the whole of `D₂^{⊗n}`**, and it proves nothing about the direct
sum over `n`.  This module removes both restrictions.

## What is proved

* `deficiencyTrivialAt_of_pushOp`, `essentiallySelfAdjointOn_of_pushOp` — essential
  self-adjointness descends along an isometry: what holds in the completion holds in the
  incomplete space it completes.
* `essentiallySelfAdjointOn_sectorDom_of_esa` — **the sector hypothesis, discharged**.  For a
  symmetric, essentially self-adjoint one-particle operator `A` on a dense domain `D` of a
  Hilbert space, `dΓ(A)⁽ⁿ⁾` *is* essentially self-adjoint on `D^{⊗n}`, for every `n`.  It is
  obtained by pulling `BookProof.EsaOneParticle.essentiallySelfAdjointOn_fockSectorDom_esa`
  back from the completed sector along `sectorEmb`.
* `essentiallySelfAdjointOn_bosonic_of_esa`, `essentiallySelfAdjointOn_fermionic_of_esa`,
  and the two core versions — the four statements of `BookProof.PermSector` with the
  sectorwise hypothesis removed: only the one-particle hypotheses remain.
* `bosonicFock`, `fermionicFock` — the two **Fock spaces**: the `ℓ²` direct sum over `n` of
  the symmetric, respectively the antisymmetric, part of `H^{⊗n}`; `bosonicFockDom`,
  `bosonicFockOp` (and the fermionic twins) — the algebraic direct sum of the sector domains
  and the second quantization `dΓ(A)` on it.
* **`bosonicFock_esa`**, **`fermionicFock_esa`** — the headline: `dΓ(A)` is essentially
  self-adjoint on the symmetric Fock space and on the antisymmetric Fock space, with
  `bosonicFock_symmetricOn` / `fermionicFock_symmetricOn` the matching symmetry statements,
  and `bosonicFockOp_single` / `fermionicFockOp_single` the identification of the operator on
  a single-particle-number state with the sector operator of `BookProof.PermSector`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.FockStatistics

open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa

noncomputable section

/-! ## 1. Essential self-adjointness descends along an isometry -/

section Pullback

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]





end Pullback

/-! ## 2. The sector hypothesis, discharged -/

section Sector

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)



end Sector

/-! ## 3. The two sectors of `H^{⊗n}`, unconditionally -/

section Statistics

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

/-- The sector derivation reduced to the **symmetric** part of `H^{⊗n}`. -/
def bosonicSectorOp (n : ℕ) :
    redDom (bosonicProj Hs n) (sectorDom Hs D n) →ₗ[ℂ] sector (bosonicProj Hs n) :=
  redOp (sectorOp Hs D A n) (isReducingProjection_bosonicProj Hs n)
    ((permRep Hs n).commutes_avgProj
      (hD := permRep_mem_sectorDom Hs D n)
      (permRep_commutes_sectorDom Hs D A n))

/-- The sector derivation reduced to the **antisymmetric** part of `H^{⊗n}`. -/
def fermionicSectorOp (n : ℕ) :
    redDom (fermionicProj Hs n) (sectorDom Hs D n) →ₗ[ℂ] sector (fermionicProj Hs n) :=
  redOp (sectorOp Hs D A n) (isReducingProjection_fermionicProj Hs n)
    ((signRep Hs n).commutes_avgProj
      (hD := signRep_mem_sectorDom Hs D n)
      (signRep_commutes_sectorDom Hs D A n))

variable (D₀ : Submodule ℂ Hs.carrier)

/-- The sector derivation reduced to the symmetrized tensor power of a one-particle core. -/
def bosonicCoreOp (n : ℕ) :
    redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n) →ₗ[ℂ] sector (bosonicProj Hs n) :=
  redOp (restrictOp (sectorOp Hs D A n) (sectorCore_le_sectorDom Hs D D₀ n))
    (isReducingProjection_bosonicProj Hs n)
    ((permRep Hs n).commutes_avgProj
      (hD := permRep_mem_sectorCore Hs D D₀ n)
      (permRep_commutes_sectorCore Hs D A D₀ n))

/-- The sector derivation reduced to the antisymmetrized tensor power of a one-particle
core. -/
def fermionicCoreOp (n : ℕ) :
    redDom (fermionicProj Hs n) (sectorCore Hs D D₀ n) →ₗ[ℂ] sector (fermionicProj Hs n) :=
  redOp (restrictOp (sectorOp Hs D A n) (sectorCore_le_sectorDom Hs D D₀ n))
    (isReducingProjection_fermionicProj Hs n)
    ((signRep Hs n).commutes_avgProj
      (hD := signRep_mem_sectorCore Hs D D₀ n)
      (signRep_commutes_sectorCore Hs D A D₀ n))

end Statistics

section StatisticsEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)





variable {D₀ : Submodule ℂ Hs.carrier}





end StatisticsEsa

/-! ## 4. The Fock spaces -/

section Fock

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
  (D₀ : Submodule ℂ Hs.carrier)

/-- **The bosonic Fock space** over `H`: the `ℓ²` direct sum, over the particle number `n`,
of the symmetric part of `H^{⊗n}`. -/
abbrev bosonicFock : Type := lp (fun n : ℕ => ↥(sector (bosonicProj Hs n))) 2

/-- **The fermionic Fock space** over `H`: the `ℓ²` direct sum, over the particle number `n`,
of the antisymmetric part of `H^{⊗n}`. -/
abbrev fermionicFock : Type := lp (fun n : ℕ => ↥(sector (fermionicProj Hs n))) 2

/-- The domain of `dΓ(A)` on the bosonic Fock space: the algebraic direct sum of the
symmetric sector domains. -/
def bosonicFockDom : Submodule ℂ (bosonicFock Hs) :=
  dsCore (fun n : ℕ => redDom (bosonicProj Hs n) (sectorDom Hs D n))

/-- The domain of `dΓ(A)` on the fermionic Fock space. -/
def fermionicFockDom : Submodule ℂ (fermionicFock Hs) :=
  dsCore (fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n))

/-- **The second quantization `dΓ(A)` on the bosonic Fock space.** -/
def bosonicFockOp : bosonicFockDom Hs D →ₗ[ℂ] bosonicFock Hs :=
  dsOp (fun n : ℕ => bosonicSectorOp Hs D A n)

/-- **The second quantization `dΓ(A)` on the fermionic Fock space.** -/
def fermionicFockOp : fermionicFockDom Hs D →ₗ[ℂ] fermionicFock Hs :=
  dsOp (fun n : ℕ => fermionicSectorOp Hs D A n)

/-- The domain of `dΓ(A)` over a one-particle core, on the bosonic Fock space. -/
def bosonicFockCoreDom : Submodule ℂ (bosonicFock Hs) :=
  dsCore (fun n : ℕ => redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n))

/-- The domain of `dΓ(A)` over a one-particle core, on the fermionic Fock space. -/
def fermionicFockCoreDom : Submodule ℂ (fermionicFock Hs) :=
  dsCore (fun n : ℕ => redDom (fermionicProj Hs n) (sectorCore Hs D D₀ n))

/-- `dΓ(A)` on the symmetric Fock space over a one-particle core. -/
def bosonicFockCoreOp : bosonicFockCoreDom Hs D D₀ →ₗ[ℂ] bosonicFock Hs :=
  dsOp (fun n : ℕ => bosonicCoreOp Hs D A D₀ n)

/-- `dΓ(A)` on the antisymmetric Fock space over a one-particle core. -/
def fermionicFockCoreOp : fermionicFockCoreDom Hs D D₀ →ₗ[ℂ] fermionicFock Hs :=
  dsOp (fun n : ℕ => fermionicCoreOp Hs D A D₀ n)

end Fock

section FockEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)









variable {D₀ : Submodule ℂ Hs.carrier}





end FockEsa

/-! ## 5. The Fock operator on a state of definite particle number -/

section Single

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)





end Single

end

end BookProof.FockStatistics


