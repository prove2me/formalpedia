-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCurveOverlap_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCurveOverlap_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:46:37.464392+00:00
-- url     : https://prove2.me/theorems/a96a98ad-3643-4987-b86e-e4d16ea41b6a
-- title:
--   FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryOverlapCore_p0
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false




/-!
# The ordinary algebraic overlap of the two N13 charts

This file begins the ordinary, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/

open Polynomial

namespace MazurProof.N13OrdinaryCurveOverlap

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev Base : Type :=
  N13IntegralInfinityChart.Base

abbrev AffineCurve : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

def xClass : AffineCurve :=
  N13GeneralizedMumfordIntegral.xClass (R := R₂) X

def yClass : AffineCurve :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)

abbrev AffineOverlap : Type :=
  Localization.Away xClass

abbrev InfinityOverlap : Type :=
  Localization.Away N13IntegralInfinityChart.tClass

def tOverlap : InfinityOverlap :=
  algebraMap InfinityCurve InfinityOverlap
    N13IntegralInfinityChart.tClass

def xOverlap : InfinityOverlap :=
  IsLocalization.Away.invSelf N13IntegralInfinityChart.tClass

def vOverlap : InfinityOverlap :=
  algebraMap InfinityCurve InfinityOverlap
    N13IntegralInfinityChart.vClass

@[simp] theorem tOverlap_mul_xOverlap :
    tOverlap * xOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := InfinityOverlap)
      N13IntegralInfinityChart.tClass

theorem xOverlap_isUnit :
    IsUnit xOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨tOverlap, by simpa [mul_comm] using tOverlap_mul_xOverlap⟩

/-- The ordinary infinity-chart equation in its two named coordinates. -/
theorem infinity_coordinate_relation :
    N13IntegralInfinityChart.vClass ^ 2 +
        (1 + N13IntegralInfinityChart.tClass ^ 2 +
            N13IntegralInfinityChart.tClass ^ 3) *
          N13IntegralInfinityChart.vClass =
      N13IntegralInfinityChart.tClass +
        N13IntegralInfinityChart.tClass ^ 2 := by
  let φ : Base →+* InfinityCurve :=
    AdjoinRoot.of N13IntegralInfinityChart.infinityCurvePoly
  let root : InfinityCurve :=
    AdjoinRoot.root N13IntegralInfinityChart.infinityCurvePoly
  have h :=
    AdjoinRoot.eval₂_root
      N13IntegralInfinityChart.infinityCurvePoly
  change
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
      φ root = 0 at h
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    N13IntegralInfinityChart.tClass,
    N13IntegralInfinityChart.vClass, φ, root] using h

theorem infinityOverlap_coordinate_relation :
    vOverlap ^ 2 +
        (1 + tOverlap ^ 2 + tOverlap ^ 3) * vOverlap =
      tOverlap + tOverlap ^ 2 := by
  simpa [tOverlap, vOverlap] using
    congrArg (algebraMap InfinityCurve InfinityOverlap)
      infinity_coordinate_relation

def coefficientToInfinityOverlap : R₂ →+* InfinityOverlap :=
  (algebraMap InfinityCurve InfinityOverlap).comp
    ((algebraMap Base InfinityCurve).comp
      (Polynomial.C : R₂ →+* Base))

def affineCoeffMap : R₂[X] →+* InfinityOverlap :=
  Polynomial.eval₂RingHom coefficientToInfinityOverlap xOverlap

@[simp] theorem affineCoeffMap_C (r : R₂) :
    affineCoeffMap (C r) = coefficientToInfinityOverlap r := by
  simp [affineCoeffMap]

@[simp] theorem affineCoeffMap_X :
    affineCoeffMap X = xOverlap := by
  simp [affineCoeffMap]

def affineYImage : InfinityOverlap :=
  xOverlap ^ 3 * vOverlap

@[simp] theorem affineCoeffMap_hPoly :
    affineCoeffMap
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      xOverlap ^ 3 + xOverlap + 1 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GeneralizedMumfordIntegral.hPoly]

@[simp] theorem affineCoeffMap_rhsPoly :
    affineCoeffMap
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      xOverlap ^ 5 + xOverlap ^ 4 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GeneralizedMumfordIntegral.rhsPoly]

theorem affineCurve_relation :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
        affineCoeffMap affineYImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
      tOverlap xOverlap vOverlap
      tOverlap_mul_xOverlap infinityOverlap_coordinate_relation
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, affineCoeffMap_hPoly,
    affineCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h

/-- Restriction of the affine coordinate ring to the ordinary infinity
principal open. -/
def affineToInfinityOverlap :
    AffineCurve →+* InfinityOverlap :=
  AdjoinRoot.lift affineCoeffMap affineYImage affineCurve_relation

@[simp] theorem affineToInfinityOverlap_of (p : R₂[X]) :
    affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)) p) =
      affineCoeffMap p := by
  exact AdjoinRoot.lift_of affineCurve_relation

@[simp] theorem affineToInfinityOverlap_xClassHom (p : R₂[X]) :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      affineCoeffMap p :=
  affineToInfinityOverlap_of p

@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk, affineCoeffMap]

@[simp] theorem affineToInfinityOverlap_yClass :
    affineToInfinityOverlap yClass = affineYImage := by
  exact AdjoinRoot.lift_root affineCurve_relation

@[simp] theorem affineToInfinityOverlap_generalized_yClass :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      affineYImage :=
  affineToInfinityOverlap_yClass

theorem affine_xClass_mapsToUnit :
    IsUnit (affineToInfinityOverlap xClass) := by
  rw [affineToInfinityOverlap_xClass]
  exact xOverlap_isUnit

/-- The induced restriction from the affine principal open to the infinity
principal open. -/
def affineOverlapToInfinityOverlap :
    AffineOverlap →+* InfinityOverlap :=
  IsLocalization.Away.lift xClass affine_xClass_mapsToUnit

@[simp] theorem affineOverlapToInfinityOverlap_algebraMap
    (z : AffineCurve) :
    affineOverlapToInfinityOverlap
        (algebraMap AffineCurve AffineOverlap z) =
      affineToInfinityOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      xClass affine_xClass_mapsToUnit z

/-! ## The reverse chart map -/

def xAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap xClass

def tAffineOverlap : AffineOverlap :=
  IsLocalization.Away.invSelf xClass

def yAffineOverlap : AffineOverlap :=
  algebraMap AffineCurve AffineOverlap yClass

@[simp] theorem xAffineOverlap_mul_tAffineOverlap :
    xAffineOverlap * tAffineOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := AffineOverlap) xClass

theorem tAffineOverlap_isUnit :
    IsUnit tAffineOverlap := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨xAffineOverlap,
      by simpa [mul_comm] using xAffineOverlap_mul_tAffineOverlap⟩

/-- The ordinary affine-chart equation in its two named coordinates. -/
theorem affine_coordinate_relation :
    yClass ^ 2 + (xClass ^ 3 + xClass + 1) * yClass =
      xClass ^ 5 + xClass ^ 4 := by
  let φ : R₂[X] →+* AffineCurve :=
    AdjoinRoot.of
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  let root : AffineCurve :=
    AdjoinRoot.root
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  have h :=
    AdjoinRoot.eval₂_root
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  change
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
      φ root = 0 at h
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    xClass, yClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.yClass,
    N13GeneralizedMumfordIntegral.mk, φ, root] using h

theorem affineOverlap_coordinate_relation :
    yAffineOverlap ^ 2 +
        (xAffineOverlap ^ 3 + xAffineOverlap + 1) *
          yAffineOverlap =
      xAffineOverlap ^ 5 + xAffineOverlap ^ 4 := by
  simpa [xAffineOverlap, yAffineOverlap] using
    congrArg (algebraMap AffineCurve AffineOverlap)
      affine_coordinate_relation

def coefficientToAffineOverlap : R₂ →+* AffineOverlap :=
  (algebraMap AffineCurve AffineOverlap).comp
    ((AdjoinRoot.of
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))).comp
        (Polynomial.C : R₂ →+* R₂[X]))

def infinityCoeffMap : Base →+* AffineOverlap :=
  Polynomial.eval₂RingHom
    coefficientToAffineOverlap tAffineOverlap

def infinityVImage : AffineOverlap :=
  tAffineOverlap ^ 3 * yAffineOverlap

@[simp] theorem infinityCoeffMap_hBase :
    infinityCoeffMap N13IntegralInfinityChart.hBase =
      1 + tAffineOverlap ^ 2 + tAffineOverlap ^ 3 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13IntegralInfinityChart.hBase]

@[simp] theorem infinityCoeffMap_rhsBase :
    infinityCoeffMap N13IntegralInfinityChart.rhsBase =
      tAffineOverlap + tAffineOverlap ^ 2 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13IntegralInfinityChart.rhsBase]

theorem infinityCurve_relation :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hBase,
    infinityCoeffMap_rhsBase]
  exact sub_eq_zero.mpr h

/-- Restriction of the infinity coordinate ring to the ordinary affine
principal open. -/
def infinityToAffineOverlap :
    InfinityCurve →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation

@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation

@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13IntegralInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13IntegralInfinityChart.tClass, infinityCoeffMap]

@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13IntegralInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation

theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit

/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_tClass_mapsToUnit

@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : InfinityCurve) :
    infinityOverlapToAffineOverlap
        (algebraMap InfinityCurve InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13IntegralInfinityChart.tClass
      infinity_tClass_mapsToUnit z

@[simp] theorem affineOverlapToInfinityOverlap_xAffineOverlap :
    affineOverlapToInfinityOverlap xAffineOverlap = xOverlap := by
  rw [xAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_xClass]

@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]

/-- The reverse overlap map sends `t⁻¹` back to `x`. -/
@[simp] theorem infinityOverlapToAffineOverlap_xOverlap :
    infinityOverlapToAffineOverlap xOverlap = xAffineOverlap := by
  have hinv :
      tAffineOverlap *
          infinityOverlapToAffineOverlap xOverlap = 1 := by
    calc
      tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap =
          infinityOverlapToAffineOverlap tOverlap *
            infinityOverlapToAffineOverlap xOverlap := by
              rw [infinityOverlapToAffineOverlap_tOverlap]
      _ =
          infinityOverlapToAffineOverlap
            (tOverlap * xOverlap) := by
              rw [map_mul]
      _ = 1 := by rw [tOverlap_mul_xOverlap, map_one]
  calc
    infinityOverlapToAffineOverlap xOverlap =
        1 * infinityOverlapToAffineOverlap xOverlap := by simp
    _ =
        (xAffineOverlap * tAffineOverlap) *
          infinityOverlapToAffineOverlap xOverlap := by
            rw [xAffineOverlap_mul_tAffineOverlap]
    _ =
        xAffineOverlap *
          (tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap) := by
              rw [mul_assoc]
    _ = xAffineOverlap := by rw [hinv, mul_one]

/-- The forward overlap map sends `x⁻¹` back to `t`. -/
@[simp] theorem affineOverlapToInfinityOverlap_tAffineOverlap :
    affineOverlapToInfinityOverlap tAffineOverlap = tOverlap := by
  have hinv :
      xOverlap *
          affineOverlapToInfinityOverlap tAffineOverlap = 1 := by
    calc
      xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap =
          affineOverlapToInfinityOverlap xAffineOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap := by
              rw [affineOverlapToInfinityOverlap_xAffineOverlap]
      _ =
          affineOverlapToInfinityOverlap
            (xAffineOverlap * tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [xAffineOverlap_mul_tAffineOverlap, map_one]
  calc
    affineOverlapToInfinityOverlap tAffineOverlap =
        1 * affineOverlapToInfinityOverlap tAffineOverlap := by simp
    _ =
        (tOverlap * xOverlap) *
          affineOverlapToInfinityOverlap tAffineOverlap := by
            rw [tOverlap_mul_xOverlap]
    _ =
        tOverlap *
          (xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap) := by
              rw [mul_assoc]
    _ = tOverlap := by rw [hinv, mul_one]

@[simp] theorem affineOverlapToInfinityOverlap_yAffineOverlap :
    affineOverlapToInfinityOverlap yAffineOverlap =
      xOverlap ^ 3 * vOverlap := by
  rw [yAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_yClass]
  rfl

@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl

@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]

@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]

/-- The reverse ordinary overlap map is a left inverse of the forward map. -/
theorem infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap :
    infinityOverlapToAffineOverlap.comp
        affineOverlapToInfinityOverlap =
      RingHom.id AffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        infinityOverlapToAffineOverlap
            (affineOverlapToInfinityOverlap xAffineOverlap) =
          xAffineOverlap
      simp
  · change
      infinityOverlapToAffineOverlap
          (affineOverlapToInfinityOverlap yAffineOverlap) =
        yAffineOverlap
    simp

/-- The forward ordinary overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13IntegralInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        affineOverlapToInfinityOverlap
            (infinityOverlapToAffineOverlap tOverlap) =
          tOverlap
      simp
  · change
      affineOverlapToInfinityOverlap
          (infinityOverlapToAffineOverlap vOverlap) =
        vOverlap
    simp

/-- The ordinary principal opens of the affine and infinity charts agree. -/
noncomputable def overlapEquiv :
    AffineOverlap ≃+* InfinityOverlap where
  toEquiv :=
    { toFun := affineOverlapToInfinityOverlap
      invFun := infinityOverlapToAffineOverlap
      left_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap z
      right_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap z }
  map_mul' := affineOverlapToInfinityOverlap.map_mul
  map_add' := affineOverlapToInfinityOverlap.map_add

@[simp] theorem overlapEquiv_apply (z : AffineOverlap) :
    overlapEquiv z = affineOverlapToInfinityOverlap z :=
  rfl

@[simp] theorem overlapEquiv_symm_apply (z : InfinityOverlap) :
    overlapEquiv.symm z = infinityOverlapToAffineOverlap z :=
  rfl

end

end MazurProof.N13OrdinaryCurveOverlap


