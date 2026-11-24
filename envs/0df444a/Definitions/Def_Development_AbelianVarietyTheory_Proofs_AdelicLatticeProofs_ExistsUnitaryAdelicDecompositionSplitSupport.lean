-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:54.087807+00:00
-- url     : https://prove2.me/theorems/bf21abe7-34dd-4475-8e5e-91f121eaf69b
-- title:
--   Exists Unitary Adelic Decomposition Split Support
-- statement:
--   Definitions and structural lemmas for Exists Unitary Adelic Decomposition Split Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_smul_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.UnRep.SplitRep
def mix {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (κ : GL (Fin n) R) : GL (Fin n) R where
  val := ε • κ.1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)
  inv := ε • (κ⁻¹).1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)
  val_inv := by
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
      Units.mul_inv, zero_smul, add_zero, zero_add, mul_one]
    rw [← add_smul]; simp
  inv_val := by
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
      Units.inv_mul, zero_smul, add_zero, zero_add, mul_one]
    rw [← add_smul]; simp
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
def inc (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom
variable [NumberField E]
end GlobalTheory.UnRep.SplitRep


