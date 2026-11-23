-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
-- name    : GroundTheory_AutomorphicForms_ReductionBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:43.420942+00:00
-- url     : https://prove2.me/theorems/25a419b2-4b3c-4b2d-8394-cabd4823ddc0
-- title:
--   Reduction Block
-- statement:
--   Definitions and structural lemmas for Reduction Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionBlock.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GroundTheory.Automorphic
namespace Reduction
section Block
variable {R : Type*} [CommRing R] {m : ℕ}
def blockOne (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i
@[simp] theorem blockOne_last_last (M : Matrix (Fin m) (Fin m) R) :
    blockOne M (Fin.last m) (Fin.last m) = 1 := by
  simp [blockOne]
@[simp] theorem blockOne_last_castSucc (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blockOne M (Fin.last m) (Fin.castSucc j) = 0 := by
  simp [blockOne]
@[simp] theorem blockOne_castSucc_last (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.last m) = 0 := by
  simp [blockOne]
@[simp] theorem blockOne_castSucc_castSucc (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.castSucc j) = M i j := by
  simp [blockOne]
theorem blockOne_mul (M N : Matrix (Fin m) (Fin m) R) :
    blockOne (M * N) = blockOne M * blockOne N := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]
theorem blockOne_one : blockOne (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
def blockOneMonoidHom : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun := blockOne
  map_one' := blockOne_one
  map_mul' := blockOne_mul
def blockOneHom : GL (Fin m) R →* GL (Fin (m + 1)) R :=
  Units.map blockOneMonoidHom
end Block
section Row
variable {F : Type*} [Field F] {m : ℕ}
def rowMatrix (x : Fin (m + 1) → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => if i = Fin.last m then x j else if i = j then 1 else 0
end Row
end Reduction
end GroundTheory.Automorphic


