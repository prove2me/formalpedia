-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:48.455148+00:00
-- url     : https://prove2.me/theorems/7351a77e-056c-4857-84cf-8596f356b709
-- title:
--   Krylov Matrix Conj Eq Of Charpoly Eq
-- statement:
--   Definitions and structural lemmas for Krylov Matrix Conj Eq Of Charpoly Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
noncomputable section
namespace GlobalTheory.LeviDesc.Krylov
def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i
end GlobalTheory.LeviDesc.Krylov


