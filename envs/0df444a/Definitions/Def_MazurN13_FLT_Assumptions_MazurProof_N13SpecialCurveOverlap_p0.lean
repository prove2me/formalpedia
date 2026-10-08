-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCurveOverlap_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialCurveOverlap_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:45.43882+00:00
-- url     : https://prove2.me/theorems/11d26278-afad-4357-ba7a-e95c0bfc7c71
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialCurveOverlap source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialCurveOverlap

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialCurveOverlap
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryOverlapCore_p0
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false




/-!
# The special algebraic overlap of the two N13 charts

This file begins the special, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/

open Polynomial

namespace MazurProof.N13SpecialCurveOverlap

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev K : Type :=
  N13SpecialInfinityChart.K

abbrev Base : Type :=
  K[X]

abbrev AffineCurve : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

abbrev CoordinateRing : Type :=
  N13SpecialInfinityChart.CoordinateRing

def xClass : AffineCurve :=
  N13GoodCoordinateRingTwo.xClass X

def yClass : AffineCurve :=
  N13GoodCoordinateRingTwo.yClass

abbrev AffineOverlap : Type :=
  Localization.Away xClass

abbrev InfinityOverlap : Type :=
  Localization.Away N13SpecialInfinityChart.tClass

def tOverlap : InfinityOverlap :=
  algebraMap CoordinateRing InfinityOverlap
    N13SpecialInfinityChart.tClass

def xOverlap : InfinityOverlap :=
  IsLocalization.Away.invSelf N13SpecialInfinityChart.tClass

def vOverlap : InfinityOverlap :=
  algebraMap CoordinateRing InfinityOverlap
    N13SpecialInfinityChart.vClass

@[simp] theorem tOverlap_mul_xOverlap :
    tOverlap * xOverlap = 1 := by
  exact
    IsLocalization.Away.mul_invSelf
      (S := InfinityOverlap)
      N13SpecialInfinityChart.tClass

theorem xOverlap_isUnit :
    IsUnit xOverlap := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨tOverlap, ?_⟩
  rw [mul_comm]
  exact tOverlap_mul_xOverlap

/-- The special infinity-chart equation in its two named coordinates. -/
theorem infinity_coordinate_relation :
    N13SpecialInfinityChart.vClass ^ 2 +
        (1 + N13SpecialInfinityChart.tClass ^ 2 +
            N13SpecialInfinityChart.tClass ^ 3) *
          N13SpecialInfinityChart.vClass =
      N13SpecialInfinityChart.tClass +
        N13SpecialInfinityChart.tClass ^ 2 := by
  let φ : Base →+* CoordinateRing :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let root : CoordinateRing :=
    AdjoinRoot.root N13SpecialInfinityChart.curvePoly
  have h :=
    AdjoinRoot.eval₂_root
      N13SpecialInfinityChart.curvePoly
  change
    N13SpecialInfinityChart.curvePoly.eval₂
      φ root = 0 at h
  simp only [N13SpecialInfinityChart.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13SpecialInfinityChart.hPoly,
    N13SpecialInfinityChart.rhsPoly,
    N13SpecialInfinityChart.tClass,
    N13SpecialInfinityChart.vClass, φ, root] using h

theorem infinityOverlap_coordinate_relation :
    vOverlap ^ 2 +
        (1 + tOverlap ^ 2 + tOverlap ^ 3) * vOverlap =
      tOverlap + tOverlap ^ 2 := by
  simpa [tOverlap, vOverlap] using
    congrArg (algebraMap CoordinateRing InfinityOverlap)
      infinity_coordinate_relation

def coefficientToInfinityOverlap : K →+* InfinityOverlap :=
  (algebraMap CoordinateRing InfinityOverlap).comp
    ((algebraMap Base CoordinateRing).comp
      (Polynomial.C : K →+* Base))

def affineCoeffMap : K[X] →+* InfinityOverlap :=
  Polynomial.eval₂RingHom coefficientToInfinityOverlap xOverlap

def affineYImage : InfinityOverlap :=
  xOverlap ^ 3 * vOverlap

@[simp] theorem affineCoeffMap_hPoly :
    affineCoeffMap
        (N13GoodCoordinateRingTwo.hPoly) =
      xOverlap ^ 3 + xOverlap + 1 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GoodCoordinateRingTwo.hPoly]

@[simp] theorem affineCoeffMap_rhsPoly :
    affineCoeffMap
        (N13GoodCoordinateRingTwo.rhsPoly) =
      xOverlap ^ 5 + xOverlap ^ 4 := by
  simp [affineCoeffMap, coefficientToInfinityOverlap,
    N13GoodCoordinateRingTwo.rhsPoly]

theorem affineCurve_relation :
    (N13GoodCoordinateRingTwo.curvePoly).eval₂
        affineCoeffMap affineYImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
      tOverlap xOverlap vOverlap
      tOverlap_mul_xOverlap infinityOverlap_coordinate_relation
  simp only [N13GoodCoordinateRingTwo.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, affineCoeffMap_hPoly,
    affineCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h

/-- Restriction of the affine coordinate ring to the special infinity
principal open. -/
def affineToInfinityOverlap :
    AffineCurve →+* InfinityOverlap :=
  AdjoinRoot.lift affineCoeffMap affineYImage affineCurve_relation

@[simp] theorem affineToInfinityOverlap_of (p : K[X]) :
    affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GoodCoordinateRingTwo.curvePoly) p) =
      affineCoeffMap p := by
  exact AdjoinRoot.lift_of affineCurve_relation

@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GoodCoordinateRingTwo.xClass,
    N13GoodCoordinateRingTwo.mk, affineCoeffMap]

@[simp] theorem affineToInfinityOverlap_yClass :
    affineToInfinityOverlap yClass = affineYImage := by
  exact AdjoinRoot.lift_root affineCurve_relation

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

/-- The special affine-chart equation in its two named coordinates. -/
theorem affine_coordinate_relation :
    yClass ^ 2 + (xClass ^ 3 + xClass + 1) * yClass =
      xClass ^ 5 + xClass ^ 4 := by
  let φ : K[X] →+* AffineCurve :=
    AdjoinRoot.of
      (N13GoodCoordinateRingTwo.curvePoly)
  let root : AffineCurve :=
    AdjoinRoot.root
      (N13GoodCoordinateRingTwo.curvePoly)
  have h :=
    AdjoinRoot.eval₂_root
      (N13GoodCoordinateRingTwo.curvePoly)
  change
    (N13GoodCoordinateRingTwo.curvePoly).eval₂
      φ root = 0 at h
  simp only [N13GoodCoordinateRingTwo.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13GoodCoordinateRingTwo.hPoly,
    N13GoodCoordinateRingTwo.rhsPoly,
    xClass, yClass,
    N13GoodCoordinateRingTwo.xClass,
    N13GoodCoordinateRingTwo.yClass,
    N13GoodCoordinateRingTwo.mk, φ, root] using h

theorem affineOverlap_coordinate_relation :
    yAffineOverlap ^ 2 +
        (xAffineOverlap ^ 3 + xAffineOverlap + 1) *
          yAffineOverlap =
      xAffineOverlap ^ 5 + xAffineOverlap ^ 4 := by
  simpa [xAffineOverlap, yAffineOverlap] using
    congrArg (algebraMap AffineCurve AffineOverlap)
      affine_coordinate_relation

def coefficientToAffineOverlap : K →+* AffineOverlap :=
  (algebraMap AffineCurve AffineOverlap).comp
    ((AdjoinRoot.of
      (N13GoodCoordinateRingTwo.curvePoly)).comp
        (Polynomial.C : K →+* K[X]))

def infinityCoeffMap : Base →+* AffineOverlap :=
  Polynomial.eval₂RingHom
    coefficientToAffineOverlap tAffineOverlap

def infinityVImage : AffineOverlap :=
  tAffineOverlap ^ 3 * yAffineOverlap

@[simp] theorem infinityCoeffMap_hPoly :
    infinityCoeffMap N13SpecialInfinityChart.hPoly =
      1 + tAffineOverlap ^ 2 + tAffineOverlap ^ 3 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13SpecialInfinityChart.hPoly]

@[simp] theorem infinityCoeffMap_rhsPoly :
    infinityCoeffMap N13SpecialInfinityChart.rhsPoly =
      tAffineOverlap + tAffineOverlap ^ 2 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13SpecialInfinityChart.rhsPoly]

theorem infinityCurve_relation :
    N13SpecialInfinityChart.curvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13SpecialInfinityChart.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hPoly,
    infinityCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h

/-- Restriction of the infinity coordinate ring to the special affine
principal open. -/
def infinityToAffineOverlap :
    CoordinateRing →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation

@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13SpecialInfinityChart.curvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation

@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13SpecialInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13SpecialInfinityChart.tClass, infinityCoeffMap]

@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13SpecialInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation

theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13SpecialInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit

/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13SpecialInfinityChart.tClass
    infinity_tClass_mapsToUnit

@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : CoordinateRing) :
    infinityOverlapToAffineOverlap
        (algebraMap CoordinateRing InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13SpecialInfinityChart.tClass
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

/-- The reverse special overlap map is a left inverse of the forward map. -/
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

/-- The forward special overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13SpecialInfinityChart.tClass)
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

/-- The special principal opens of the affine and infinity charts agree. -/
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

end MazurProof.N13SpecialCurveOverlap


