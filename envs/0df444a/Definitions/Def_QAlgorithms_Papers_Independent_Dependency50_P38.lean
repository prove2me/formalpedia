-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38
-- name    : QAlgorithms_Papers_Independent_Dependency50_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:13:23.976915+00:00
-- url     : https://prove2.me/theorems/edc30fe6-9236-456a-9bdb-3f94bc01f107
-- title:
--   Definitions for Classification and implementation of unitary-equivariant and permutation-invariant quantum channels
-- statement:
--   The objects the formalized statements of *Classification and implementation of unitary-equivariant and permutation-invariant quantum channels* (arXiv:2510.08154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `vectorizeInputFirst`: arXiv:2510.08154v1, PDF p.34, Remark 11: the canonical tensor swap puts Definition 7's vectorization in input-first order for Fact 1. Mathlib's `Matrix.vec` already uses this order; `WithLp.toLp` only equips the same coordinates with the Euclidean-space type.
-- source:
--   Classification and implementation of unitary-equivariant and permutation-invariant quantum channels, arXiv:2510.08154v1, https://arxiv.org/abs/2510.08154v1

import Mathlib.LinearAlgebra.Matrix.Vec
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Statements from Mancinska and Theil, arXiv:2510.08154v1.
Only Proposition 4 and Appendix Fact 1 are stated here. The assigned unit's
HARD.md and GAPS.json account for the remaining numbered results.
Choi matrices are unnormalized and input first. No frozen definition is changed.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P38

open scoped Matrix ComplexConjugate

/-- One-dimensional identity channel has Choi matrix entry one. -/
example : QAlgorithms.Papers.Independent.Information100.P34.choi
    (fun A : Matrix (Fin 1) (Fin 1) ℂ => A) (0, 0) (0, 0) = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P34.choi, Matrix.single]

/-- A rectangular one-entry map retains its entry under vectorization. -/
example (z : ℂ) :
    (WithLp.toLp 2 (Matrix.vec (Matrix.transpose
      (fun _ : Fin 1 => fun _ : Fin 1 => z)))) (0, 0) = z := rfl

/-- arXiv:2510.08154v1, PDF p.34, Remark 11: the canonical tensor swap
puts Definition 7's vectorization in input-first order for Fact 1.
Mathlib's `Matrix.vec` already uses this order; `WithLp.toLp` only equips
the same coordinates with the Euclidean-space type. -/
def vectorizeInputFirst {a b : Type*} (M : Matrix b a ℂ) :
    EuclideanSpace ℂ (a × b) :=
  WithLp.toLp 2 (Matrix.vec M)

/-- The swap sends a one-by-two map's second entry to input position one. -/
example (M : Matrix (Fin 1) (Fin 2) ℂ) :
    vectorizeInputFirst M (1, 0) = M 0 1 := rfl

end QAlgorithms.Papers.Independent.Dependency50.P38


