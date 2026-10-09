-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphContraction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphContraction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:17:39.095008+00:00
-- url     : https://prove2.me/theorems/2fda17e9-b997-4438-8b97-7f5b1956e4dc
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalInfinityContraction_p0

set_option autoImplicit false




/-!
# Contraction of a vertical N13 infinity graph

The direct reciprocal kernel maps the integral infinity chart into the
original Mumford quotient.  Since the infinity coordinate `t` maps to a
unit, this map extends to the ordinary overlap.  Its kernel there is the
extension of the direct kernel.

For a recovered vertical graph, the three-generated affine closure has the
same overlap ideal and already makes `x` a unit modulo the ideal.  Contracting
from the overlap therefore identifies this affine closure with the canonical
vertical contraction of the original generic Mumford ideal.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityVerticalGraphContraction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model

abbrev AffineCurve : Type :=
  N13OrdinaryCurveOverlap.AffineCurve

abbrev InfinityCurve : Type :=
  N13OrdinaryCurveOverlap.InfinityCurve

abbrev InfinityOverlap : Type :=
  N13OrdinaryCurveOverlap.InfinityOverlap

abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph

abbrev GenericQuotient
    (D : SexticMumford.Mumford Model) : Type :=
  N13ReciprocalInfinityContraction.GenericQuotient D

/-- The reciprocal infinity coordinate maps to a unit in the original
generic Mumford quotient. -/
theorem tbar_isUnit
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    IsUnit (N13ReciprocalInfinityContraction.tbar D) := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨N13ReciprocalInfinityContraction.xbar D,
      by
        simpa [mul_comm] using
          N13ReciprocalInfinityContraction.xbar_mul_tbar
            D hdeg h0⟩

/-- Extension of the direct infinity-chart map to the ordinary overlap. -/
def infinityOverlapToGenericQuotient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityOverlap →+* GenericQuotient D :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    (by
      rw [
        N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass
          D hdeg h0]
      exact tbar_isUnit D hdeg h0)

/-- The overlap extension restricts to the original direct infinity map. -/
@[simp] theorem infinityOverlapToGenericQuotient_comp_infinity
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (infinityOverlapToGenericQuotient D hdeg h0).comp
        (algebraMap InfinityCurve InfinityOverlap) =
      N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient
        D hdeg h0 := by
  exact
    IsLocalization.Away.lift_comp
      N13IntegralInfinityChart.tClass
      (by
        rw [
          N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass
            D hdeg h0]
        exact tbar_isUnit D hdeg h0)

/-- The named overlap coordinate `t` maps to the reciprocal quotient
coordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_tOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.tOverlap =
      N13ReciprocalInfinityContraction.tbar D := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    ← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass]

/-- The named overlap coordinate `v` maps to the reciprocal quotient
ordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_vOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.vOverlap =
      N13ReciprocalInfinityContraction.vbar D := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    ← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_vClass]

/-- The inverse overlap coordinate `x=t⁻¹` maps to the affine quotient
coordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_xOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.xOverlap =
      N13ReciprocalInfinityContraction.xbar D := by
  let φ :=
    infinityOverlapToGenericQuotient D hdeg h0
  have htx :
      N13ReciprocalInfinityContraction.tbar D *
          φ N13OrdinaryCurveOverlap.xOverlap =
        1 := by
    calc
      N13ReciprocalInfinityContraction.tbar D *
            φ N13OrdinaryCurveOverlap.xOverlap =
          φ N13OrdinaryCurveOverlap.tOverlap *
            φ N13OrdinaryCurveOverlap.xOverlap := by
              rw [infinityOverlapToGenericQuotient_tOverlap]
      _ =
          φ
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by rw [map_mul]
      _ = 1 := by
        rw [N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap, map_one]
  calc
    φ N13OrdinaryCurveOverlap.xOverlap =
        1 * φ N13OrdinaryCurveOverlap.xOverlap := by simp
    _ =
        (N13ReciprocalInfinityContraction.xbar D *
            N13ReciprocalInfinityContraction.tbar D) *
          φ N13OrdinaryCurveOverlap.xOverlap := by
            rw [
              N13ReciprocalInfinityContraction.xbar_mul_tbar
                D hdeg h0]
    _ = N13ReciprocalInfinityContraction.xbar D := by
      rw [mul_assoc, htx, mul_one]

/-- Integral coefficients on the overlap map to their images in the
generic Mumford quotient. -/
@[simp] theorem infinityOverlapToGenericQuotient_coefficient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (r : R₂) :
    infinityOverlapToGenericQuotient D hdeg h0
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r) =
      N13ReciprocalInfinityContraction.coefficientToGenericQuotient
        D r := by
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    infinityOverlapToGenericQuotient D hdeg h0
        ((algebraMap InfinityCurve InfinityOverlap)
          (algebraMap R₂ InfinityCurve r)) =
      _
  rw [← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_algebraMap]
  rfl

/-- The affine integral model maps to the original Mumford quotient by
generic coefficient extension followed by quotient projection. -/
def affineToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    AffineCurve →+* GenericQuotient D :=
  (Ideal.Quotient.mk
      (N13ReciprocalInfinityContraction.genericIdeal D)).comp
    N13TwoAdicCoordinateBaseChange.integralToSextic

/-- The affine horizontal polynomial class evaluates at the quotient
coordinate `x̄`. -/
@[simp] theorem affineToGenericQuotient_xClassHom
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    affineToGenericQuotient D
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      aeval (N13ReciprocalInfinityContraction.xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) := by
  change
    Ideal.Quotient.mk
        (N13ReciprocalInfinityContraction.genericIdeal D)
        (N13GoodSexticCoordinateEquiv.toSextic
          (N13TwoAdicCoordinateBaseChange.extendCoordinate
            (N13GeneralizedMumfordIntegral.xClass p))) =
      _
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass]
  exact
    (N13ReciprocalInfinityContraction.aeval_xbar
      D (N13TwoAdicCoordinateBaseChange.mapPoly p)).symm

/-- The affine integral ordinate maps to the good-model ordinate in the
generic Mumford quotient. -/
@[simp] theorem affineToGenericQuotient_yClass
    (D : SexticMumford.Mumford Model) :
    affineToGenericQuotient D
        N13GeneralizedMumfordIntegral.yClass =
      N13ReciprocalInfinityContraction.goodYbar D := by
  rw [affineToGenericQuotient, RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.extend_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_yClass]
  rfl

/-- The affine and infinity descriptions of the direct map agree on the
ordinary overlap. -/
theorem overlap_affine_map_compatibility
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (infinityOverlapToGenericQuotient D hdeg h0).comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      affineToGenericQuotient D := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineToInfinityOverlap_of]
      change
        infinityOverlapToGenericQuotient D hdeg h0
            (N13OrdinaryCurveOverlap.affineCoeffMap (C r)) =
          affineToGenericQuotient D
            (N13GeneralizedMumfordIntegral.xClassHom (C r))
      rw [N13OrdinaryCurveOverlap.affineCoeffMap_C,
        infinityOverlapToGenericQuotient_coefficient,
        affineToGenericQuotient_xClassHom,
        N13ReciprocalInfinityContraction.aeval_mapPoly_xbar]
      simp [N13ReciprocalInfinityContraction.coefficientToGenericQuotient]
    · change
        ((infinityOverlapToGenericQuotient D hdeg h0).comp
            N13OrdinaryCurveOverlap.affineToInfinityOverlap)
            (N13GeneralizedMumfordIntegral.xClassHom X) =
          affineToGenericQuotient D
            (N13GeneralizedMumfordIntegral.xClassHom X)
      rw [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
        N13OrdinaryCurveOverlap.affineCoeffMap_X]
      rw [infinityOverlapToGenericQuotient_xOverlap,
        affineToGenericQuotient_xClassHom]
      simp [N13TwoAdicCoordinateBaseChange.mapPoly]
  · change
      ((infinityOverlapToGenericQuotient D hdeg h0).comp
          N13OrdinaryCurveOverlap.affineToInfinityOverlap)
          N13GeneralizedMumfordIntegral.yClass =
        affineToGenericQuotient D
          N13GeneralizedMumfordIntegral.yClass
    rw [RingHom.comp_apply,
      N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass]
    rw [N13OrdinaryCurveOverlap.affineYImage,
      map_mul, map_pow,
      infinityOverlapToGenericQuotient_xOverlap,
      infinityOverlapToGenericQuotient_vOverlap,
      affineToGenericQuotient_yClass]
    change
      N13ReciprocalInfinityContraction.xbar D ^ 3 *
          (N13ReciprocalInfinityContraction.tbar D ^ 3 *
            N13ReciprocalInfinityContraction.goodYbar D) =
        N13ReciprocalInfinityContraction.goodYbar D
    rw [← mul_assoc, ← mul_pow,
      N13ReciprocalInfinityContraction.xbar_mul_tbar D hdeg h0,
      one_pow, one_mul]

/-- The kernel of the overlap map is the extension of the direct integral
infinity kernel. -/
theorem map_integralInfinityIdeal_eq_overlapKernel
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0) =
      RingHom.ker
        (infinityOverlapToGenericQuotient D hdeg h0) := by
  rw [N13ReciprocalInfinityContraction.integralInfinityIdeal]
  exact
    N13LocalizationIdealPatch.map_ker_eq_ker_of_isLocalization
      (A := InfinityCurve) (B := InfinityOverlap)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      (N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient
        D hdeg h0)
      (infinityOverlapToGenericQuotient D hdeg h0)
      (infinityOverlapToGenericQuotient_comp_infinity D hdeg h0)

/-- The kernel of the affine quotient map is the canonical contraction of
the original generic Mumford ideal. -/
theorem affineToGenericQuotient_ker
    (D : SexticMumford.Mumford Model) :
    RingHom.ker (affineToGenericQuotient D) =
      N13IntegralModelContraction.contractIdeal
        (N13ReciprocalInfinityContraction.genericIdeal D) := by
  change
    RingHom.ker
        ((Ideal.Quotient.mk
          (N13ReciprocalInfinityContraction.genericIdeal D)).comp
          N13TwoAdicCoordinateBaseChange.integralToSextic) =
      Ideal.comap
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13ReciprocalInfinityContraction.genericIdeal D)
  rw [← RingHom.comap_ker, Ideal.mk_ker]

/-- A recovered vertical graph gives exactly the canonical affine
contraction of the original generic Mumford ideal. -/
theorem contractIdeal_eq_affineIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    N13IntegralModelContraction.contractIdeal
        (N13ReciprocalInfinityContraction.genericIdeal D) =
      N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E := by
  let Ia :=
    N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E
  let f :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g : InfinityCurve →+* InfinityOverlap :=
    algebraMap InfinityCurve InfinityOverlap
  let q :=
    infinityOverlapToGenericQuotient D hdeg h0
  calc
    N13IntegralModelContraction.contractIdeal
          (N13ReciprocalInfinityContraction.genericIdeal D) =
        RingHom.ker (affineToGenericQuotient D) :=
      (affineToGenericQuotient_ker D).symm
    _ = Ideal.comap f (RingHom.ker q) := by
      rw [RingHom.comap_ker,
        overlap_affine_map_compatibility D hdeg h0]
    _ =
        Ideal.comap f
          (Ideal.map g
            (N13ReciprocalInfinityContraction.integralInfinityIdeal
              D hdeg h0)) := by
      rw [map_integralInfinityIdeal_eq_overlapKernel D hdeg h0]
    _ = Ideal.comap f (Ideal.map g E.ideal) := by rw [hI]
    _ = Ideal.comap f (Ideal.map f Ia) := by
      rw [
        N13IntegralInfinityVerticalGraphTwoChart.ideals_agree_on_overlap
          u E huDegree.le hmDegree huMem]
    _ = Ia := by
      exact
        N13IntegralInfinityGraphSaturation.affineOverlapContracted_of_xUnitMod
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_xUnitMod
            u E hu huDegree)

/-- A recovered vertical reciprocal branch is a proper two-chart spread of
the original generic Mumford ideal.  The infinity component is the direct
kernel itself, while exact contraction and vertical localization identify
the affine generic fibre with the original graph rather than only with an
isomorphic Picard class. -/
theorem exists_twoChartLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
      L.infinityIdeal =
          N13ReciprocalInfinityContraction.integralInfinityIdeal
            D hdeg h0 ∧
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          N13ReciprocalInfinityContraction.genericIdeal D := by
  let L :=
    N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
      u E hu huDegree hmDegree huMem
  refine ⟨L, ?_, ?_⟩
  · change E.ideal =
      N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0
    exact hI.symm
  · change
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E) =
        N13ReciprocalInfinityContraction.genericIdeal D
    rw [← contractIdeal_eq_affineIdeal
        D hdeg h0 u E hu huDegree hmDegree huMem hI,
      N13IntegralModelContraction.map_contractIdeal]

/-- The recovered vertical branch has an invertible canonical divisorial
hull on the affine integral model. -/
theorem divisorialHull_isUnit
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹))
    (E : VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13ReciprocalInfinityContraction.genericIdeal D)) := by
  let u :=
    N13ReciprocalQuadraticReflection.integralReciprocal a b
  have hu :
      u.Monic :=
    N13ReciprocalQuadraticReflection.integralReciprocal_monic a b
  have huDegree :
      u.natDegree = 2 :=
    N13ReciprocalQuadraticReflection.integralReciprocal_natDegree a b
  have huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal := by
    rw [← hI]
    exact
      N13ReciprocalInfinityContraction.reciprocal_mem_integralInfinityIdeal
        D hdeg h0 a b hm
  exact
    N13IntegralGraphSpread.divisorialHull_isUnit_of_contractIdeal_eq_isUnit
      (N13ReciprocalInfinityContraction.genericIdeal D)
      (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E)
      (contractIdeal_eq_affineIdeal
        D hdeg h0 u E hu huDegree hmDegree huMem hI)
      (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_isUnit
        u E hu huDegree hmDegree huMem)

end

end MazurProof.N13IntegralInfinityVerticalGraphContraction


