-- Prove2me | Definitions.Def_ChapterPauliCommutant
-- name    : ChapterPauliCommutant
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:50:51.881738+00:00
-- url     : https://prove2.me/theorems/3a76bf03-69b5-40a8-852b-756e808ef02b
-- title:
--   Chapter PauliCommutant
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPauliCommutant.lean`): generated def bundle for ChapterPauliCommutant. See BookProof/ChapterPauliCommutant.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPauliCommutant.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter A, §A.3 — the commutant of the concrete Majorana/Dirac γ-matrices

`BookProof/ChapterA3b.lean` takes the **Pauli fundamental theorem** (Note 36) as
an `EXTERNAL` named hypothesis `PauliFundamental`, because in the stated
generality (all complex Clifford sets on `ℂ⁴`) it is not available in Mathlib.

This file discharges the `EXTERNAL` flag **for the fixed 4×4 model** built in
`BookProof/ChapterA3.lean`: it proves, by an explicit finite computation, the
Schur-type statement

  *any complex `4×4` matrix commuting with all four Majorana matrices `iγ^μ`
  is a scalar multiple of the identity,*

together with its immediate consequences:

* `mgamma_commutant_scalar` / `mgamma_commutant_iff` — the commutant of
  `{iγ⁰, iγ¹, iγ², iγ³}` in `Mat(4, ℂ)` is exactly `ℂ · 1`;
* `mgamma5_of_commutes` — such a matrix automatically commutes with `iγ⁵` too;
* `dgamma_commutant_scalar` — the same for the Dirac matrices `γ^μ = -i(iγ^μ)`;
* `mgamma_conjugation_unique_up_to_scalar` — the **uniqueness clause** of the
  Pauli fundamental theorem for the concrete family: two invertible matrices
  conjugating the `iγ^μ` to the same set differ by a nonzero scalar;
* `mgamma_conj_eq_self_iff` — the stabiliser of the family under conjugation is
  the group of scalars.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis is used**.
-/

open Matrix

namespace BookProof.ChapterA3













/-! ## Irreducibility of the concrete Majorana representation

The commutant computation above is exactly the input Schur's lemma needs.  Here
it is turned around: because the Majorana family is closed under the adjoint (up
to a sign), the orthogonal projection onto an invariant subspace commutes with
every `iγ^μ`, hence is a scalar, hence the subspace is `⊥` or `⊤`.
-/

/-- The Euclidean space `ℂ⁴` carrying the Majorana representation. -/
noncomputable abbrev MajoranaSpace := EuclideanSpace ℂ (Fin 4)

/-- The Majorana matrices acting as linear maps on `ℂ⁴`. -/
noncomputable def mgammaLin (μ : Fin 4) : MajoranaSpace →ₗ[ℂ] MajoranaSpace :=
  Matrix.toEuclideanLin (mgamma μ)













end BookProof.ChapterA3


