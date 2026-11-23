-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:19.568848+00:00
-- url     : https://prove2.me/theorems/6e632006-8863-4bae-9477-d526215efa72
-- title:
--   Exists Unimodular Pos Def Adjoint Action
-- statement:
--   Definitions and structural lemmas for Exists Unimodular Pos Def Adjoint Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnimodularPosDefAdjointAction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
namespace GlobalTheory
section
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]
def zarhinAction {R : Type} [CommRing R] (σ : R →+* R) (ρ0 : R →+* Matrix n n ℤ) :
    R →+* Matrix ((n × q) ⊕ (n × q)) ((n × q) ⊕ (n × q)) ℤ where
  toFun a := fromBlocks ((ρ0 (σ a))ᵀ ⊗ₖ (1 : Matrix q q ℤ)) 0 0 (ρ0 a ⊗ₖ (1 : Matrix q q ℤ))
  map_one' := by simp
  map_mul' a b := by
    rw [fromBlocks_multiply, mul_comm a b, map_mul σ, map_mul ρ0, transpose_mul, mul_comm b a,
      map_mul ρ0]
    simp [← mul_kronecker_mul]
  map_zero' := by simp
  map_add' a b := by
    simp [fromBlocks_add, add_kronecker, transpose_add]
end
end GlobalTheory


