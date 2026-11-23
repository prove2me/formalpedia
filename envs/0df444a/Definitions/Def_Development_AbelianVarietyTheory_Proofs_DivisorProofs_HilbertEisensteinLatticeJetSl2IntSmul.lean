-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSl2IntSmul
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSl2IntSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:19.782466+00:00
-- url     : https://prove2.me/theorems/7d795e64-08a8-467c-b45f-41f759b723dd
-- title:
--   Hilbert Eisenstein Lattice Jet Sl2 Int Smul
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Lattice Jet Sl2 Int Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeJetSl2IntSmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HilbFam.JetModular
def rowEquiv (F : Type) [Field F] (γ : SL(2, ℤ)) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  LinearEquiv.ofLinear
    (Matrix.vecMulLinear ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (Matrix.vecMulLinear (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp)
end GlobalTheory.HilbFam.JetModular


