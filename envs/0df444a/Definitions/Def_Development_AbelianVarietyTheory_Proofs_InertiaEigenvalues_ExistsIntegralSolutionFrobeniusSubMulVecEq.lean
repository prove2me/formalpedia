-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:52.965405+00:00
-- url     : https://prove2.me/theorems/96cf8a4b-6e40-4d7e-b832-08c623012a76
-- title:
--   Exists Integral Solution Frobenius Sub Mul Vec Eq
-- statement:
--   Definitions and structural lemmas for Exists Integral Solution Frobenius Sub Mul Vec Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
def backPoly {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) : k[X] :=
  Nat.rec X (fun j P => P ^ q - C (c (n - j)) * X) j
end GlobalTheory.PMonE.LangOnto
end


