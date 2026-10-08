-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticCoordinateEquiv_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticCoordinateEquiv_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:57:48.099604+00:00
-- url     : https://prove2.me/theorems/227a7d0c-35a0-4327-b424-6b4ced049031
-- title:
--   FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Mumford_p0

set_option autoImplicit false




/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/

open Polynomial

namespace MazurProof.N13GoodSexticCoordinateEquiv

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

abbrev M : SexticMumford.Model K :=
  N13Mumford.model K

abbrev GoodRing : Type u :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := K)

abbrev SexticRing : Type u :=
  N13Mumford.CoordinateRing K

def goodXHom : K[X] →+* GoodRing (K := K) :=
  N13GeneralizedMumfordIntegral.xClassHom

def sexticXHom : K[X] →+* SexticRing (K := K) :=
  AdjoinRoot.of (SexticMumford.curvePoly (M (K := K)))

@[simp] theorem goodXHom_apply (p : K[X]) :
    goodXHom (K := K) p =
      N13GeneralizedMumfordIntegral.xClass p := rfl

@[simp] theorem sexticXHom_apply (p : K[X]) :
    sexticXHom (K := K) p =
      SexticMumford.xClass (M (K := K)) p := rfl

abbrev hPoly : K[X] :=
  N13GeneralizedMumfordIntegral.hPoly

abbrev rhsPoly : K[X] :=
  N13GeneralizedMumfordIntegral.rhsPoly

/-- The polynomial identity behind completion of the square. -/
theorem sextic_eq_h_sq_add_four_rhs :
    N13Mumford.f K = hPoly ^ 2 + 4 * rhsPoly := by
  simp only [N13Mumford.f, hPoly, rhsPoly,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

/-- The good `y` coordinate inside the sextic coordinate ring. -/
def goodYInSextic : SexticRing (K := K) :=
  (1 / 2 : K) •
    (SexticMumford.yClass (M (K := K)) -
      sexticXHom (K := K) hPoly)

/-- The sextic `Y` coordinate inside the good coordinate ring. -/
def sexticYInGood : GoodRing (K := K) :=
  2 * N13GeneralizedMumfordIntegral.yClass +
    goodXHom (K := K) hPoly

private theorem goodYInSextic_root :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (sexticXHom (K := K)) (goodYInSextic (K := K)) = 0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  have hy := SexticMumford.yClass_sq (M (K := K))
  change
    SexticMumford.yClass (M (K := K)) ^ 2 =
      sexticXHom (K := K) (N13Mumford.f K) at hy
  rw [sextic_eq_h_sq_add_four_rhs (K := K)] at hy
  simp only [map_add, map_mul, map_pow, map_ofNat] at hy
  let a : SexticRing (K := K) :=
    (algebraMap K (SexticRing (K := K))) (1 / 2)
  let Y : SexticRing (K := K) :=
    SexticMumford.yClass (M (K := K))
  let H : SexticRing (K := K) :=
    sexticXHom (K := K) (hPoly (K := K))
  let R : SexticRing (K := K) :=
    sexticXHom (K := K) (rhsPoly (K := K))
  simp only [goodYInSextic, Algebra.smul_def]
  change (a * (Y - H)) ^ 2 + H * (a * (Y - H)) - R = 0
  have hy' : Y ^ 2 = H ^ 2 + 4 * R := hy
  have ha : 2 * a = 1 := by
    dsimp only [a]
    rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
      ← map_mul]
    norm_num
  linear_combination
    a ^ 2 * hy' +
      (-a * Y * H + a * H ^ 2 + (2 * a + 1) * R) * ha

private theorem good_root_relation :
    N13GeneralizedMumfordIntegral.yClass ^ 2 +
        goodXHom (K := K) (hPoly (K := K)) *
          N13GeneralizedMumfordIntegral.yClass -
      goodXHom (K := K) (rhsPoly (K := K)) = 0 := by
  apply sub_eq_zero.mpr
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13GeneralizedMumfordIntegral.curvePoly]
  ring

private theorem sexticYInGood_root :
    (SexticMumford.curvePoly (M (K := K))).eval₂
      (goodXHom (K := K)) (sexticYInGood (K := K)) = 0 := by
  simp only [SexticMumford.curvePoly,
    eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change
    sexticYInGood (K := K) ^ 2 -
      goodXHom (K := K) (N13Mumford.f K) = 0
  rw [sextic_eq_h_sq_add_four_rhs (K := K)]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  unfold sexticYInGood
  linear_combination 4 * good_root_relation (K := K)

/-- Completion of the square as a ring homomorphism from the good model to
the sextic model. -/
def toSextic :
    GoodRing (K := K) →+* SexticRing (K := K) :=
  AdjoinRoot.lift (sexticXHom (K := K))
    (goodYInSextic (K := K))
    (goodYInSextic_root (K := K))

/-- The inverse change of variables. -/
def toGood :
    SexticRing (K := K) →+* GoodRing (K := K) :=
  AdjoinRoot.lift (goodXHom (K := K))
    (sexticYInGood (K := K))
    (sexticYInGood_root (K := K))

@[simp] theorem toSextic_xClass (p : K[X]) :
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p := by
  change
    toSextic (K := K)
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := K)) p) =
      sexticXHom (K := K) p
  exact AdjoinRoot.lift_of (goodYInSextic_root (K := K))

@[simp] theorem toSextic_algebraMap (z : K) :
    toSextic (K := K)
        (algebraMap K (GoodRing (K := K)) z) =
      algebraMap K (SexticRing (K := K)) z := by
  change
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass (C z)) =
      SexticMumford.xClass (M (K := K)) (C z)
  exact toSextic_xClass (K := K) (C z)

@[simp] theorem toSextic_yClass :
    toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  AdjoinRoot.lift_root (goodYInSextic_root (K := K))

@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (sexticYInGood_root (K := K))

@[simp] theorem toGood_algebraMap (z : K) :
    toGood (K := K)
        (algebraMap K (SexticRing (K := K)) z) =
      algebraMap K (GoodRing (K := K)) z := by
  change
    toGood (K := K)
        (SexticMumford.xClass (M (K := K)) (C z)) =
      N13GeneralizedMumfordIntegral.xClass (C z)
  exact toGood_xClass (K := K) (C z)

@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (sexticYInGood_root (K := K))

private theorem invTwo_mul_two_good :
    (algebraMap K (GoodRing (K := K))) (2 : K)⁻¹ *
        (2 : GoodRing (K := K)) = 1 := by
  rw [← map_ofNat
      (algebraMap K (GoodRing (K := K))) 2,
    ← map_mul]
  norm_num

private theorem two_mul_invTwo_sextic :
    (2 : SexticRing (K := K)) *
        (algebraMap K (SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
    ← map_mul]
  norm_num

private theorem toGood_comp_toSextic :
    (toGood (K := K)).comp (toSextic (K := K)) =
      RingHom.id (GoodRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toGood (K := K)
          (toSextic (K := K) (goodXHom (K := K) p)) =
        goodXHom (K := K) p
    rw [goodXHom_apply, toSextic_xClass, toGood_xClass]
  · change
      toGood (K := K) (toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass) =
          N13GeneralizedMumfordIntegral.yClass
    rw [toSextic_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [← mul_assoc, invTwo_mul_two_good (K := K), one_mul]

private theorem toSextic_comp_toGood :
    (toSextic (K := K)).comp (toGood (K := K)) =
      RingHom.id (SexticRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toSextic (K := K)
          (toGood (K := K) (sexticXHom (K := K) p)) =
        sexticXHom (K := K) p
    rw [sexticXHom_apply, toGood_xClass, toSextic_xClass]
  · change
      toSextic (K := K)
          (toGood (K := K)
            (SexticMumford.yClass (M (K := K)))) =
        SexticMumford.yClass (M (K := K))
    rw [toGood_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [map_ofNat, ← mul_assoc,
      two_mul_invTwo_sextic (K := K)]
    ring

/-- The coordinate-ring isomorphism induced by completion of the square. -/
def coordinateRingEquiv :
    GoodRing (K := K) ≃+* SexticRing (K := K) where
  toFun := toSextic (K := K)
  invFun := toGood (K := K)
  left_inv z := by
    have h :=
      DFunLike.congr_fun (toGood_comp_toSextic (K := K)) z
    simpa using h
  right_inv z := by
    have h :=
      DFunLike.congr_fun (toSextic_comp_toGood (K := K)) z
    simpa using h
  map_mul' := map_mul (toSextic (K := K))
  map_add' := map_add (toSextic (K := K))

@[simp] theorem coordinateRingEquiv_xClass (p : K[X]) :
    coordinateRingEquiv (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p :=
  toSextic_xClass (K := K) p

@[simp] theorem coordinateRingEquiv_yClass :
    coordinateRingEquiv (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  toSextic_yClass (K := K)

end

end MazurProof.N13GoodSexticCoordinateEquiv


