-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasis
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:25.71164+00:00
-- url     : https://prove2.me/theorems/3c708bd7-d21c-422e-b3a7-a7fd3570a2e9
-- title:
--   Hermitian Endo Matrix Rational In Lattice Basis
-- statement:
--   Definitions and structural lemmas for Hermitian Endo Matrix Rational In Lattice Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianEndoMatrixRationalInLatticeBasis.lean

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
namespace GlobalTheory
def imFormRight {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r w := by
    simp [star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im]
def imFormLeft {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [add_dotProduct]
  map_smul' r z := by
    simp [smul_dotProduct, Complex.smul_im]
end GlobalTheory


