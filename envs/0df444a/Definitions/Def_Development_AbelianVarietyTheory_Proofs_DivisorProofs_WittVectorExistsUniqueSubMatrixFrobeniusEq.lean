-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:27.856312+00:00
-- url     : https://prove2.me/theorems/49c5cd24-44c1-48cf-bb11-a730236a8e40
-- title:
--   Witt Vector Exists Unique Sub Matrix Frobenius Eq
-- statement:
--   Definitions and structural lemmas for Witt Vector Exists Unique Sub Matrix Frobenius Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]
noncomputable def F (M : Matrix ι ι (WittVector p R)) (v : ι → WittVector p R) :
    ι → WittVector p R :=
  v - M.mulVec (fun k => WittVector.frobenius (v k))
variable {M : Matrix ι ι (WittVector p R)}
end GlobalTheory.WittSolve
namespace GlobalTheory
end GlobalTheory


