-- Prove2me | Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
-- name    : QAlgorithms_Defs_TensorPermutationRepresentations
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:00.77473+00:00
-- url     : https://prove2.me/theorems/2520c26f-f194-4271-9e9d-4df51b432e52
-- title:
--   TensorPermutationRepresentations
-- statement:
--   TensorPermutationRepresentations
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TensorPermutationRepresentations.lean

import Definitions.Def_QAlgorithms_Defs_SchurShapes
noncomputable section

namespace QAlgorithms.Schur

/-- Tensor-factor permutation action |j> ↦ |j ∘ pi^{-1}>; this is computed from the
permutation, rather than an arbitrary representation (1508.01797 p.4, §III). -/
def tensorPermutation (d n : ℕ) (pi : Equiv.Perm (Fin n)) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun y x => if y = x ∘ pi.symm then 1 else 0

example (d n : ℕ) : tensorPermutation d n 1 = 1 := by
  ext y x
  rfl

example (x : Fin 2 → Fin 2) :
    tensorPermutation 2 2 (Equiv.swap 0 1) (x ∘ Equiv.swap 0 1) x = 1 := by
  simp [tensorPermutation]

end QAlgorithms.Schur


