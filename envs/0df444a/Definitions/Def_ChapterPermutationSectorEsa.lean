-- Prove2me | Definitions.Def_ChapterPermutationSectorEsa
-- name    : ChapterPermutationSectorEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T15:35:43.130091+00:00
-- url     : https://prove2.me/theorems/bea3c722-a819-4a72-b208-638d8037474b
-- title:
--   Chapter PermutationSectorEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPermutationSectorEsa.lean`): generated def bundle for ChapterPermutationSectorEsa. See BookProof/ChapterPermutationSectorEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPermutationSectorEsa.lean

import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterTensorGraphCore
import Mathlib


/-!
# The bosonic and the fermionic `n`-particle sector

`BookProof.TensorCore` proves that a one-particle core lifts to a core of the sector
derivation `dΓ(A)⁽ⁿ⁾` on the **full** tensor power `H^{⊗n}`;
`BookProof.TwoParticleSector` reduces that operator to the two halves of `H^{⊗2}`;
`BookProof.GroupAverage` reduces an operator to the invariant sector of a finite group of
unitaries; and `BookProof.TensorPerm` constructs the action of the symmetric group
`Equiv.Perm (Fin n)` on `H^{⊗n}`.  This module puts the four together and closes the
symmetrization programme for **every** particle number:

> **The `n`-particle sectors.**  The permutation action preserves the domain `D₂^{⊗n}` of the
> sector derivation and the tensor power `D^{⊗n}` of a one-particle core, and it commutes
> with the derivation.  Hence `dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the symmetric
> (bosonic) sector and on the antisymmetric (fermionic) sector — on the domain and on the
> core — as soon as it is essentially self-adjoint on `D₂^{⊗n}`.

The commutation is proved once and for all by *structural* induction: the two elementary
isometries out of which every permutation operator is built — the exchange `swapFirst` of the
first two factors and the lift `liftTail` of an operator to the last `n` factors — both
preserve the inclusion of the domain, the derivation and the core, and those three properties
are stable under composition.

## Contents

* `Good` — the conjunction of the three compatibilities, for a pair of operators on
  `D₂^{⊗n}` and on `H^{⊗n}`; `good_liftTail`, `good_swapFirst`, `good_trans`, `good_swap0`
  and **`good_permOp`**.
* `permOp_mem_sectorDom`, `permOp_mem_sectorCore`, `sectorOp_permOp` — the consequences for
  the operator `sectorOp = dΓ(A)⁽ⁿ⁾` inside `H^{⊗n}`.
* `bosonicProj`, `fermionicProj` — the symmetrizer `|Sₙ|⁻¹ Σ_σ U_σ` and the antisymmetrizer
  `|Sₙ|⁻¹ Σ_σ sgn(σ) U_σ`, with `mem_bosonicSector_iff` and `mem_fermionicSector_iff`.
* **`essentiallySelfAdjointOn_bosonic`**, **`essentiallySelfAdjointOn_fermionic`** — the two
  sector statements on the domain `D₂^{⊗n}`, and **`essentiallySelfAdjointOn_bosonic_core`**,
  **`essentiallySelfAdjointOn_fermionic_core`** on the symmetrized and the antisymmetrized
  one-particle core `D^{⊗n}`, for any core `D` of `A`; `symmetricOn_bosonic`,
  `symmetricOn_fermionic`.
* `exists_ne_zero_bosonic`, `exists_ne_zero_fermionic` — non-vacuity witnesses (the `n`-th
  power `a ⊗ ⋯ ⊗ a` of a core vector; the Slater determinant of `n` pairwise orthogonal core
  vectors).
* `permOp_two_eq_swapH` — consistency with the two-particle chapter: for `n = 2` the
  transposition operator is the swap used there.

Nothing is assumed: the module contains no `axiom` and no `sorry`.

The hypothesis `EssentiallySelfAdjointOn (sectorDom …) (sectorOp …)` carried by the four
headline statements below, and the passage from the fixed particle number to the direct sum
over all of them, are both settled in `BookProof.FockStatistics`
(`BookProof/ChapterFockStatisticsEsa.lean` and
`BookProof/ChapterFockStatisticsCompletion.lean`): the hypothesis is a theorem for a
symmetric, essentially self-adjoint one-particle operator on a dense domain of a Hilbert
space, and `dΓ(A)` is then essentially self-adjoint on the bosonic and on the fermionic Fock
space.
-/

namespace BookProof.PermSector

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section



variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

/-! ## The three compatibilities -/

/-- A pair of operators — one on the algebraic tensor power `D₂^{⊗n}` of the domain, one on
`H^{⊗n}` — is **good** when the first is carried to the second by the inclusion, when the two
intertwine the sector derivation, and when the first preserves the tensor power `D^{⊗n}` of
the one-particle core. -/
structure Good (n : ℕ)
    (uD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier)
    (uH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow n).carrier) : Prop where
  /-- compatibility with the inclusion of the domain -/
  incl : ∀ t, inclPow Hs D₂ n (uD t) = uH (inclPow Hs D₂ n t)
  /-- commutation with the sector derivation -/
  der : ∀ t, derPow Hs D₂ A n (uD t) = uH (derPow Hs D₂ A n t)
  /-- preservation of the core tensor power -/
  core : ∀ t ∈ corePow Hs D₂ D n, uD t ∈ corePow Hs D₂ D n













/-! ## The consequences for the sector operator -/















/-! ## The two sectors -/

/-- The **symmetrizer** of `H^{⊗n}`: the average of the permutation action. -/
def bosonicProj (n : ℕ) : (Hs.pow n).carrier →ₗ[ℂ] (Hs.pow n).carrier :=
  (permRep Hs n).avgProj

/-- The **antisymmetrizer** of `H^{⊗n}`: the average of the sign-twisted permutation
action. -/
def fermionicProj (n : ℕ) : (Hs.pow n).carrier →ₗ[ℂ] (Hs.pow n).carrier :=
  (signRep Hs n).avgProj









/-! ## The action preserves the domain and the core, and commutes with the operator -/

















/-! ## Essential self-adjointness on the two sectors -/









/-! ## Symmetry of the sector operators -/





/-! ## Pure tensors inside the domain and the core -/







/-! ## Non-vacuity of the two sectors -/





/-! ## Consistency with the two-particle chapter -/



end

end BookProof.PermSector


