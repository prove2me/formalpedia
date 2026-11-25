-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:45.799438+00:00
-- url     : https://prove2.me/theorems/74a05f0a-ba17-5efe-8826-2781b19cd538
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Embedding.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_algebraMap_padic
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_liftFracWitt
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_surjective_of_frobenius
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_section_algebraMap
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_section
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_IsUnitBall_frobenius_surjective
import Theorems.Thm_Reformulated_AutPerF_OCK_coe_ofInteger
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_formallyEtale_of_isAlgebraic
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
import Theorems.Thm_Reformulated_AutPerF_fracWitt_hom_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.OCK.coe_ofInteger
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]
namespace BdRPlus
def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)
variable {p O}
theorem thetaC_apply (x : BdRPlus p O) :
    thetaC p O x = IsUnitBall.awayEquiv O p (theta p O x) := rfl
@[simp] theorem thetaC_algebraMap (x : Ainf p O) :
    thetaC p O (algebraMap _ _ x) = (Ainf.theta p O x : C) := by
  rw [thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap,
    AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]
variable [IsAlgClosed C]
section General
variable {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
  [Algebra.IsAlgebraic F L]
def sectionC (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) :
    L →+* BdRPlus p O :=
  haveI := formallyEtale_of_isAlgebraic F L
  «section» (AinfInv.theta_surjective_of_frobenius p (IsUnitBall.frobenius_surjective O p)) ι
    ((IsUnitBall.awayEquiv O p).symm.toRingEquiv.toRingHom.comp j) (fun a => by
      change (IsUnitBall.awayEquiv O p).symm (j _) = _
      rw [AlgEquiv.symm_apply_eq, hj]
      rfl)
@[simp] theorem thetaC_sectionC (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) (x : L) :
    thetaC p O (sectionC ι j hj x) = j x := by
  haveI := formallyEtale_of_isAlgebraic F L
  rw [thetaC_apply, sectionC, theta_section]
  exact (IsUnitBall.awayEquiv O p).apply_symm_apply _
@[simp] theorem sectionC_algebraMap (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) (a : F) :
    sectionC ι j hj (algebraMap F L a) = algebraMap _ _ (ι a) := by
  haveI := formallyEtale_of_isAlgebraic F L
  rw [sectionC, section_algebraMap]
end General
end BdRPlus
section Padic
variable [NormedAlgebra ℚ_[p] C]
omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] in

def IsUnitBall.ofPadicInt : ℤ_[p] →+* O :=
  ((algebraMap ℚ_[p] C).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict _ fun x =>
    (IsUnitBall.mem_iff _).2 (by
      rw [RingHom.comp_apply, norm_algebraMap']; exact x.norm_le_one)
variable {p O} in

@[simp] theorem BdRPlus.thetaC_algebraMap_padic (a : ℚ_[p]) :
    BdRPlus.thetaC p O (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] C a := by
  have := AinfInv.theta_algebraMap_padic (IsUnitBall.ofPadicInt p O)
    ((IsUnitBall.awayEquiv O p).symm.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] C))
    (fun a => by
      change (IsUnitBall.awayEquiv O p).symm _ = _
      rw [AlgEquiv.symm_apply_eq, IsUnitBall.awayEquiv_algebraMap]
      rfl) a
  rw [BdRPlus.thetaC_apply, IsScalarTower.algebraMap_apply ℚ_[p] (AinfInv p O),
    BdRPlus.theta_algebraMap, this]
  exact (IsUnitBall.awayEquiv O p).apply_symm_apply _
variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]
def BdRPlus.padicSection (j : L →ₐ[ℚ_[p]] C) : L →ₐ[ℚ_[p]] BdRPlus p O :=
  { BdRPlus.sectionC (algebraMap ℚ_[p] (AinfInv p O)) (j : L →+* C) (fun a => by
      rw [← IsScalarTower.algebraMap_apply, BdRPlus.thetaC_algebraMap_padic]
      exact j.commutes a) with
    commutes' := fun a => BdRPlus.sectionC_algebraMap _ _ _ a }
variable {p O}
@[simp] theorem BdRPlus.thetaC_padicSection (j : L →ₐ[ℚ_[p]] C) (x : L) :
    BdRPlus.thetaC p O (BdRPlus.padicSection p O j x) = j x := by
  refine BdRPlus.thetaC_sectionC (algebraMap ℚ_[p] (AinfInv p O)) (j : L →+* C) (fun a => ?_) x
  rw [← IsScalarTower.algebraMap_apply, BdRPlus.thetaC_algebraMap_padic]
  exact j.commutes a
end Padic
section Witt
variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]
omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] [IsUnitBall O] [IsAlgClosed C] in
theorem charZero_wittVector : CharZero (WittVector p k) := by
  refine ⟨fun m n h => ?_⟩
  have hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))
instance : CharZero (FractionRing (WittVector p k)) :=
  haveI := charZero_wittVector p (k := k)
  inferInstance
variable {p O}
theorem BdRPlus.thetaC_liftFracWitt (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a)
    (a : FractionRing (WittVector p k)) :
    j (algebraMap _ L a) = BdRPlus.thetaC p O (algebraMap _ _ (AinfInv.liftFracWitt p g a)) :=
  RingHom.congr_fun (fracWitt_hom_ext (f := j.comp (algebraMap _ L))
    (g := (BdRPlus.thetaC p O).comp ((algebraMap _ _).comp (AinfInv.liftFracWitt p g)))
    (fun a => by
      simp only [RingHom.comp_apply]
      rw [hj, BdRPlus.thetaC_apply, BdRPlus.theta_algebraMap, AinfInv.theta_liftFracWitt,
        IsUnitBall.awayEquiv_algebraMap])) a
def BdRPlus.wittSection (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a) :
    L →+* BdRPlus p O :=
  BdRPlus.sectionC (AinfInv.liftFracWitt p g) j (BdRPlus.thetaC_liftFracWitt g j hj)
end Witt
def padicAlgClToBdRPlus : PadicAlgCl p →ₐ[ℚ_[p]] BdRPlus p (PadicComplexInt p) :=
  BdRPlus.padicSection p (PadicComplexInt p) (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
end Reformulated.AutPerF


