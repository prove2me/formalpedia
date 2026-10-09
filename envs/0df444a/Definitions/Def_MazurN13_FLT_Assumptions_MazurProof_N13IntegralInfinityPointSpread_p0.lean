-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityPointSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityPointSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:34:41.026968+00:00
-- url     : https://prove2.me/theorems/eeda663e-2927-4aca-af3b-17c39d833c9c
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GeneralizedGraphIdealCore_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCurveProperties_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0
import Mathlib.RingTheory.FractionalIdeal.Inverse

set_option autoImplicit false




/-!
# Integral point ideals on the N13 infinity chart

An integral point `(t₀,v₀)` on the ordinary infinity chart with
`t₀ ≡ 0 mod 2` defines the linear graph ideal

`(t-t₀, v-v₀)`.

Its generalized Jacobian in the ordinate direction reduces to `1`, hence
is a two-adic unit.  The abstract graph-ideal product theorem then gives an
explicit inverse for this point ideal.  This is the infinity-chart analogue
of the integral affine semigraph construction.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityPointSpread

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13ProperCurveReduction.Z₂

abbrev Base : Type :=
  N13IntegralInfinityChart.Base

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev FunctionField : Type :=
  FractionRing InfinityCurve

abbrev InfinityFractionalIdeal : Type :=
  FractionalIdeal InfinityCurve⁰ FunctionField

abbrev IntegralInfinityPoint : Type :=
  {p : R₂ × R₂ //
    N13GoodModelTwo.InfinityChartEquation p.1 p.2}

def xClassHom : Base →+* InfinityCurve :=
  AdjoinRoot.of N13IntegralInfinityChart.infinityCurvePoly

def yClass : InfinityCurve :=
  N13IntegralInfinityChart.vClass

@[simp] theorem xClassHom_X :
    xClassHom X = N13IntegralInfinityChart.tClass := rfl

theorem yClass_relation :
    yClass ^ 2 +
        xClassHom N13IntegralInfinityChart.hBase * yClass =
      xClassHom N13IntegralInfinityChart.rhsBase := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13IntegralInfinityChart.infinityCurvePoly]
  ring

def pointU (P : IntegralInfinityPoint) : Base :=
  X - C P.1.1

def pointV (P : IntegralInfinityPoint) : Base :=
  C P.1.2

def pointResidual (P : IntegralInfinityPoint) : Base :=
  pointV P ^ 2 +
    N13IntegralInfinityChart.hBase * pointV P -
    N13IntegralInfinityChart.rhsBase

theorem pointResidual_eval (P : IntegralInfinityPoint) :
    (pointResidual P).eval P.1.1 = 0 := by
  simpa [pointResidual, pointV,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    N13GoodModelTwo.InfinityChartEquation,
    sub_eq_zero] using P.2

theorem pointU_dvd_pointResidual (P : IntegralInfinityPoint) :
    pointU P ∣ pointResidual P := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointResidual P) (a := P.1.1)
  simpa [pointU, pointResidual_eval] using h

def pointW (P : IntegralInfinityPoint) : Base :=
  Classical.choose (pointU_dvd_pointResidual P)

theorem pointResidual_eq_mul_pointW (P : IntegralInfinityPoint) :
    pointResidual P = pointU P * pointW P :=
  Classical.choose_spec (pointU_dvd_pointResidual P)

def pointSemiGraph (P : IntegralInfinityPoint) :
    GeneralizedGraphIdealCore.SemiGraph
      N13IntegralInfinityChart.hBase
      N13IntegralInfinityChart.rhsBase where
  u := pointU P
  v := pointV P
  w := pointW P
  curve_eq := pointResidual_eq_mul_pointW P

/-- The ordinate Jacobian evaluated at the integral infinity point. -/
def pointJacobianValue (P : IntegralInfinityPoint) : R₂ :=
  2 * P.1.2 +
    (1 + P.1.1 ^ 2 + P.1.1 ^ 3)

theorem pointJacobianValue_toZMod
    (P : IntegralInfinityPoint) :
    PadicInt.toZMod (pointJacobianValue P) = 1 := by
  have htwo :
      PadicInt.toZMod (2 : R₂) = 0 := by
    calc
      PadicInt.toZMod (2 : R₂) = (2 : ZMod 2) :=
        map_natCast (PadicInt.toZMod (p := 2)) 2
      _ = 0 := ZMod.natCast_self 2
  calc
    PadicInt.toZMod (pointJacobianValue P) =
      PadicInt.toZMod (2 : R₂) * PadicInt.toZMod P.1.2 +
          (1 + PadicInt.toZMod P.1.1 ^ 2 +
            PadicInt.toZMod P.1.1 ^ 3) := by
      simp only [pointJacobianValue, map_add, map_mul, map_one, map_pow]
    _ = 1 := by
      let t : ZMod 2 := PadicInt.toZMod P.1.1
      have ht2 : t ^ 2 = t :=
        ZMod.pow_card t
      have ht3 : t ^ 3 = t := by
        rw [show t ^ 3 = t ^ 2 * t by ring,
          ht2, ← pow_two, ht2]
      rw [htwo, zero_mul, zero_add]
      change 1 + t ^ 2 + t ^ 3 = 1
      rw [ht2, ht3]
      linear_combination (ZMod.natCast_self 2) * t

/-- At every integral infinity-chart point, the ordinate Jacobian is a
unit.  On the special fibre `t²=t`, so `1+t²+t³=1`. -/
theorem pointJacobianValue_isUnit
    (P : IntegralInfinityPoint) :
    IsUnit (pointJacobianValue P) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hzero
  have hmap :=
    congrArg
      (PadicInt.residueField (p := 2))
      hzero
  have hto :
      PadicInt.toZMod (pointJacobianValue P) = 0 := by
    simpa [PadicInt.toZMod_eq_residueField_comp_residue] using hmap
  rw [pointJacobianValue_toZMod P] at hto
  exact one_ne_zero hto

def pointJacobian (P : IntegralInfinityPoint) : Base :=
  2 * pointV P + N13IntegralInfinityChart.hBase

@[simp] theorem pointJacobian_eval (P : IntegralInfinityPoint) :
    (pointJacobian P).eval P.1.1 = pointJacobianValue P := by
  simp [pointJacobian, pointJacobianValue, pointV,
    N13IntegralInfinityChart.hBase]

theorem pointU_dvd_pointJacobian_sub_value
    (P : IntegralInfinityPoint) :
    pointU P ∣ pointJacobian P - C (pointJacobianValue P) := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := pointJacobian P) (a := P.1.1)
  simpa [pointU, pointJacobian_eval] using h

def pointJacobianQuotient (P : IntegralInfinityPoint) : Base :=
  Classical.choose (pointU_dvd_pointJacobian_sub_value P)

theorem pointJacobian_sub_value_eq
    (P : IntegralInfinityPoint) :
    pointJacobian P - C (pointJacobianValue P) =
      pointU P * pointJacobianQuotient P :=
  Classical.choose_spec (pointU_dvd_pointJacobian_sub_value P)

/-- The unit ordinate derivative supplies the exact graph Bézout identity. -/
theorem point_bezout
    (P : IntegralInfinityPoint) :
    ∃ a b c : Base,
      a * pointU P +
          b *
            (2 * pointV P +
              N13IntegralInfinityChart.hBase) +
          c * pointW P = 1 := by
  let e : R₂ˣ := (pointJacobianValue_isUnit P).unit
  let b : Base := C ((e⁻¹ : R₂ˣ) : R₂)
  refine
    ⟨-(b * pointJacobianQuotient P), b, 0, ?_⟩
  have he : (e : R₂) = pointJacobianValue P :=
    (pointJacobianValue_isUnit P).unit_spec
  have hj := pointJacobian_sub_value_eq P
  change
    -(b * pointJacobianQuotient P) * pointU P +
        b * pointJacobian P + 0 * pointW P = 1
  rw [zero_mul, add_zero]
  calc
    -(b * pointJacobianQuotient P) * pointU P +
          b * pointJacobian P =
        b * C (pointJacobianValue P) := by
      linear_combination b * hj
    _ = C (((e⁻¹ : R₂ˣ) : R₂) * pointJacobianValue P) := by
      simp [b]
    _ = 1 := by
      rw [← he]
      simp

def pointIdeal (P : IntegralInfinityPoint) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    xClassHom yClass (pointU P) (pointV P)

def conjugatePointIdeal
    (P : IntegralInfinityPoint) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    xClassHom yClass (pointU P)
      (GeneralizedGraphIdealCore.conjugateV
        N13IntegralInfinityChart.hBase (pointV P))

/-- The point ideal times its hyperelliptic conjugate is `(t-t₀)`. -/
theorem pointIdeal_mul_conjugate
    (P : IntegralInfinityPoint) :
    pointIdeal P * conjugatePointIdeal P =
      Ideal.span ({xClassHom (pointU P)} : Set InfinityCurve) := by
  exact
    GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass
      N13IntegralInfinityChart.hBase
      N13IntegralInfinityChart.rhsBase
      (pointSemiGraph P)
      yClass_relation
      (point_bezout P)

theorem infinityCurvePoly_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num

theorem xClassHom_injective :
    Function.Injective xClassHom := by
  exact
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [infinityCurvePoly_degree]; norm_num)

theorem xClassHom_pointU_ne_zero (P : IntegralInfinityPoint) :
    xClassHom (pointU P) ≠ 0 := by
  rw [← map_zero xClassHom]
  apply xClassHom_injective.ne
  exact (monic_X_sub_C P.1.1).ne_zero

/-- The integral infinity-chart point ideal is invertible. -/
theorem pointIdeal_isUnit
    (P : IntegralInfinityPoint) :
    IsUnit (pointIdeal P : InfinityFractionalIdeal) := by
  refine
    ⟨Units.mkOfMulEqOne
      (pointIdeal P : InfinityFractionalIdeal)
      ((conjugatePointIdeal P : InfinityFractionalIdeal) *
        (Ideal.span
          ({xClassHom (pointU P)} : Set InfinityCurve) :
            InfinityFractionalIdeal)⁻¹)
      ?_, rfl⟩
  rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul,
    pointIdeal_mul_conjugate P]
  exact
    FractionalIdeal.coe_ideal_span_singleton_mul_inv
      FunctionField (xClassHom_pointU_ne_zero P)

/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/

def affineU (P : IntegralInfinityPoint) : R₂[X] :=
  1 - C P.1.1 * X

def affineV (P : IntegralInfinityPoint) : R₂[X] :=
  C P.1.2 * X ^ 3

def affineW (P : IntegralInfinityPoint) : R₂[X] :=
  C P.1.2 * X ^ 3 +
    C (P.1.2 - 1 + P.1.1 * P.1.2) * X ^ 4 +
    C (-1 - P.1.1 + P.1.1 * P.1.2 +
      P.1.1 ^ 2 * P.1.2) * X ^ 5

/-- Weighted homogenization of the infinity point equation gives the exact
affine graph factorization. -/
theorem affine_curve_eq (P : IntegralInfinityPoint) :
    affineV P ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV P -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
      affineU P * affineW P := by
  have hp :
      P.1.2 ^ 2 +
          (1 + P.1.1 ^ 2 + P.1.1 ^ 3) * P.1.2 -
          (P.1.1 + P.1.1 ^ 2) = 0 :=
    sub_eq_zero.mpr P.2
  have hpC :=
    congrArg (Polynomial.C : R₂ →+* R₂[X]) hp
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at hpC
  unfold affineU affineV affineW
  simp only [N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    map_sub, map_add, map_mul, map_pow, map_one, map_neg]
  linear_combination X ^ 6 * hpC

def affineGraphData (P : IntegralInfinityPoint) :
    N13IntegralGraphJacobian.GraphData where
  u := affineU P
  v := affineV P
  w := affineW P
  curve_eq := affine_curve_eq P

theorem affineU_ne_zero (P : IntegralInfinityPoint) :
    affineU P ≠ 0 := by
  intro hzero
  have h :=
    congrArg (Polynomial.eval (0 : R₂)) hzero
  simpa [affineU] using h

def affinePointIdeal
    (P : IntegralInfinityPoint) :
    Ideal N13IntegralGraphJacobian.IntegralRing :=
  GeneralizedGraphIdealCore.graphIdeal
    N13GeneralizedMumfordIntegral.xClassHom
    N13GeneralizedMumfordIntegral.yClass
    (affineU P) (affineV P)

/-- The affine closure of an escaping infinity point is also an invertible
fractional ideal, despite its nonmonic horizontal equation. -/
theorem affinePointIdeal_isUnit
    (P : IntegralInfinityPoint) :
    IsUnit
      (affinePointIdeal P :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  exact
    N13IntegralGraphJacobian.graphIdeal_isUnit
      (affineGraphData P) (affineU_ne_zero P)

private theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        (u : A) (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.mul_mem_left _
        (v : A) (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have h :
          (u : A) * a ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((u⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm
    · rw [hz]
      have h :
          (v : A) * b ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.subset_span (by simp)
      have hm := Ideal.mul_mem_left _
        ((v⁻¹ : Aˣ) : A) h
      simpa [mul_assoc] using hm

@[simp] theorem pointU_on_overlap (P : IntegralInfinityPoint) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (xClassHom (pointU P)) =
      N13OrdinaryCurveOverlap.tOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 := by
  simp [pointU, xClassHom,
    N13OrdinaryCurveOverlap.tOverlap,
    N13IntegralInfinityChart.tClass,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]

@[simp] theorem pointV_on_overlap (P : IntegralInfinityPoint) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (yClass - xClassHom (pointV P)) =
      N13OrdinaryCurveOverlap.vOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 := by
  simp [pointV, yClass, xClassHom,
    N13OrdinaryCurveOverlap.vOverlap,
    N13IntegralInfinityChart.vClass,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]

theorem affineU_on_overlap (P : IntegralInfinityPoint) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (affineU P)) =
      N13OrdinaryCurveOverlap.xOverlap *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap
            (xClassHom (pointU P))) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    pointU_on_overlap]
  simp only [affineU, map_sub, map_one, map_mul,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  rw [mul_sub, mul_comm N13OrdinaryCurveOverlap.xOverlap
      N13OrdinaryCurveOverlap.tOverlap,
    N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap]
  ring

theorem affineV_on_overlap (P : IntegralInfinityPoint) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (GeneralizedGraphIdealCore.ySubClass
          N13GeneralizedMumfordIntegral.xClassHom
          N13GeneralizedMumfordIntegral.yClass
          (affineV P)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap
            (yClass - xClassHom (pointV P))) := by
  rw [pointV_on_overlap]
  simp only [GeneralizedGraphIdealCore.ySubClass, map_sub,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  simp [affineV,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  ring

/-- The two local point ideals agree on the ordinary overlap.  Their two
generators differ only by the units `x` and `x³`. -/
theorem pointIdeals_agree_on_overlap (P : IntegralInfinityPoint) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P) =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        (pointIdeal P) := by
  simp only [affinePointIdeal, pointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    Ideal.map_span, Set.image_pair]
  rw [affineU_on_overlap P, affineV_on_overlap P]
  let ux :
      N13OrdinaryCurveOverlap.InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hux3 :
      ((ux ^ 3 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 3 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 3 =
        N13OrdinaryCurveOverlap.xOverlap ^ 3
    rw [hux]
  have hs :=
    span_pair_unit_mul
      ux (ux ^ 3)
      (algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap
          (xClassHom (pointU P)))
      (algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap
          (yClass - xClassHom (pointV P)))
  rw [hux, hux3] at hs
  exact hs

/-- Concrete two-chart presentation of an invertible line on the ordinary
integral N13 model. -/
structure TwoChartLine where
  affineIdeal : Ideal N13IntegralGraphJacobian.IntegralRing
  infinityIdeal : Ideal InfinityCurve
  affine_isUnit :
    IsUnit
      (affineIdeal :
        N13IntegralGraphJacobian.IntegralFractionalIdeal)
  infinity_isUnit :
    IsUnit (infinityIdeal : InfinityFractionalIdeal)
  overlap_eq :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap affineIdeal =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        infinityIdeal

/-- The horizontal section through an infinity-chart integral point is an
actual invertible two-chart line. -/
def pointLine
    (P : IntegralInfinityPoint) :
    TwoChartLine where
  affineIdeal := affinePointIdeal P
  infinityIdeal := pointIdeal P
  affine_isUnit := affinePointIdeal_isUnit P
  infinity_isUnit := pointIdeal_isUnit P
  overlap_eq := pointIdeals_agree_on_overlap P

theorem nonintegralLift_t_residue_eq_zero
    (x y : N13ProperCurveReduction.Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    PadicInt.toZMod
        (N13ProperCurveReduction.nonintegralInfinityLift
          x y hx hxy).1.1 = 0 := by
  change
    PadicInt.toZMod
      (N13LocalDlogRegimes.inverseIntegralPart x hx) = 0
  exact
    N13LocalDlogRegimes.inverseIntegralPart_residue_eq_zero x hx

/-- Every nonintegral affine point therefore has a canonical integral
two-chart point line, with no affine escape. -/
def nonintegralPointLine
    (x y : N13ProperCurveReduction.Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    TwoChartLine :=
  pointLine
    (N13ProperCurveReduction.nonintegralInfinityLift
      x y hx hxy)

abbrev Model : SexticMumford.Model N13ProperCurveReduction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M
    (K := N13ProperCurveReduction.Q₂)

/-- The generic fibre of the affine half of the point line is its
coefficient-extended, completed-square sextic graph. -/
theorem map_affinePointIdeal (P : IntegralInfinityPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affinePointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineU P))
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV P))) := by
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    ← Ideal.map_map]
  change
    Ideal.map N13GoodSexticCoordinateEquiv.toSextic
        (Ideal.map N13TwoAdicCoordinateBaseChange.extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (affineU P) (affineV P))) = _
  rw [N13TwoAdicCoordinateBaseChange.map_mumfordIdeal,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]

end

end MazurProof.N13IntegralInfinityPointSpread


