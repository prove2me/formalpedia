-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:18:09.869709+00:00
-- url     : https://prove2.me/theorems/5dea38c7-da07-4ddb-b0df-ea9eca1a5d3f
-- title:
--   Primitive Semilinear Lift Base Change Bijective
-- statement:
--   Definitions and structural lemmas for Primitive Semilinear Lift Base Change Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk


set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace PDiv
section PrimBaseChange
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']
theorem counit_comp_cartierBaseChange :
    (counitAlgHom R' (CartierDual R' (R' ⊗[R] A))).comp
        ((CartierDual.baseChange R R' A).toAlgEquiv : R' ⊗[R] CartierDual R A →ₐ[R'] _) =
      AugCot.baseChangeAug R' (counitAlgHom R (CartierDual R A)) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    simp [Algebra.TensorProduct.one_def, Algebra.smul_def, mul_comm]
def cotBaseChange :
    Cot R' (CartierDual R' (R' ⊗[R] A)) ≃ₗ[R'] R' ⊗[R] Cot R (CartierDual R A) :=
  ((AugCot.baseChangeEquiv R' (counitAlgHom R (CartierDual R A))).trans
    (AugCot.congr (CartierDual.baseChange R R' A).toAlgEquiv
      (counit_comp_cartierBaseChange R'))).symm
end PrimBaseChange
end PDiv
end GlobalTheory


