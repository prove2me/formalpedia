-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:08.813124+00:00
-- url     : https://prove2.me/theorems/254568a8-c00e-58a1-99bf-56db707770e5
-- title:
--   PCone Ring Laurent
-- statement:
--   Definitions and structural lemmas for PCone Ring Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
namespace ConeRingLaurent
variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)
def tProd : MvPolynomial K (DehomRing i) := ∏ k, X k
abbrev Laurent := Localization.Away (tProd i)
def laurentToConeRing : MvPolynomial K (DehomRing i) →+* ConeRing i :=
  eval₂Hom (ratioMap i) fun k => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)
theorem laurentToConeRing_tProd : laurentToConeRing i (tProd i) = algebraMap _ (ConeRing i) (coneUnit i) := by
  simp [laurentToConeRing, tProd, coneUnit, map_prod]
def toCone : Laurent i →+* ConeRing i :=
  IsLocalization.Away.lift (tProd i) (g := laurentToConeRing i) (by
    rw [laurentToConeRing_tProd]; exact IsLocalization.Away.algebraMap_isUnit (coneUnit i))
def coneToLaurentPolynomial : MvPolynomial (Σ k, ι k) ℂ →+* Laurent i :=
  eval₂Hom ((algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C.comp (algebraMap ℂ (DehomRing i))))
    fun p => algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (C (dehom i (X p)) * X p.1)
theorem coneToLaurent_X_self (k : K) :
    coneToLaurentPolynomial i (X ⟨k, i k⟩) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X k) := by
  simp [coneToLaurentPolynomial, dehom_X_self]
theorem coneToLaurent_coneUnit :
    coneToLaurentPolynomial i (coneUnit i) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (tProd i) := by
  rw [coneUnit, map_prod]
  exact (Finset.prod_congr rfl fun k _ => coneToLaurent_X_self i k).trans (map_prod _ _ _).symm
def fromCone : ConeRing i →+* Laurent i :=
  IsLocalization.Away.lift (coneUnit i) (g := coneToLaurentPolynomial i) (by
    rw [coneToLaurent_coneUnit]; exact IsLocalization.Away.algebraMap_isUnit (tProd i))
theorem ratioMap_algebraMap (c : ℂ) :
    ratioMap i (algebraMap ℂ (DehomRing i) c) = algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
  rw [← AlgHom.commutes (dehom i) c, ratioMap_dehom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq]
theorem toCone_comp_fromCone : (toCone i).comp (fromCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneUnit i))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_C, toCone, laurentToConeRing]
    exact ratioMap_algebraMap i c
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_X', toCone, map_mul, laurentToConeRing, eval₂Hom_C]
    rw [ratioMap_dehom, coneRatio, aeval_X, mul_right_comm, (isUnit_coneX i p.1).val_inv_mul, one_mul]
theorem fromCone_algebraMap (f : MvPolynomial (Σ k, ι k) ℂ) :
    fromCone i (algebraMap _ (ConeRing i) f) = coneToLaurentPolynomial i f :=
  IsLocalization.Away.lift_eq _ _ _
theorem fromCone_comp_ratioMap :
    (fromCone i).comp (ratioMap i) =
      (algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C : DehomRing i →+* MvPolynomial K (DehomRing i)) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio, aeval_C,
      IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq,
      fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_C]
    rfl
  · intro p
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_X', map_mul, ← mul_assoc]
    have hu : fromCone i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) =
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) := by
      rw [IsUnit.unit_spec, fromCone_algebraMap, coneToLaurent_X_self]
    have hinv : fromCone i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    rw [mul_comm _ (algebraMap _ _ (C _)), mul_assoc, hinv, mul_one]
theorem fromCone_comp_toCone : (fromCone i).comp (toCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tProd i))
  apply MvPolynomial.ringHom_ext
  · intro y
    have h := RingHom.congr_fun (fromCone_comp_ratioMap i) y
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing,
      eval₂Hom_C] at h ⊢
    exact h
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing, eval₂Hom_X']
    rw [fromCone_algebraMap, coneToLaurent_X_self]
def laurentEquiv : Laurent i ≃+* ConeRing i :=
  RingEquiv.ofRingHom (toCone i) (fromCone i) (toCone_comp_fromCone i) (fromCone_comp_toCone i)
end ConeRingLaurent
end GroundTheory.Heights₂.Heights.Targets


