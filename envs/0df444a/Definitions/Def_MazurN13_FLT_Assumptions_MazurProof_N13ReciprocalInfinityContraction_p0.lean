-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalInfinityContraction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalInfinityContraction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:15:19.436991+00:00
-- url     : https://prove2.me/theorems/60304762-04ff-4c54-891c-be8183f085ee
-- title:
--   FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ContractQuotientXYBasis_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryOverlapCore_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientFiniteness_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientVerticalFlatness_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalQuadraticReflection_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TensorSpecialFiber_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberNoEscape_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoGeneratorFiberBasis_p0
import Mathlib.LinearAlgebra.Dimension.Localization

set_option autoImplicit false




/-!
# The reciprocal N13 divisor on the integral infinity chart

For a quadratic generic Mumford graph with nonzero constant coefficient,
the class of the affine coordinate is invertible in its graph quotient.
Its explicit inverse is the infinity coordinate `t`, and `t³y` is the
ordinary infinity ordinate.  The ordinary overlap identity therefore
defines a canonical map from the integral infinity chart into the original
generic Mumford quotient.  Its kernel is the integral infinity ideal used
for rank-two recovery.
-/

open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct

namespace MazurProof.N13ReciprocalInfinityContraction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev Q₂ : Type :=
  N13CanonicalContractionQuotient.Q₂

abbrev k : Type :=
  N13SpecialInfinityChart.K

abbrev κ : Type :=
  IsLocalRing.ResidueField R₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model

abbrev InfinityRing : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev SpecialRing : Type :=
  N13SpecialInfinityChart.CoordinateRing

abbrev RationalRing : Type :=
  N13CanonicalContractionQuotient.RationalRing

local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13IntegralInfinityReduction.reduceBase.toAlgebra

def genericIdeal
    (D : SexticMumford.Mumford Model) :
    Ideal RationalRing :=
  N13CanonicalContractionQuotient.graphIdeal D.toSemi

abbrev GenericQuotient
    (D : SexticMumford.Mumford Model) : Type :=
  RationalRing ⧸ genericIdeal D

def xbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  Ideal.Quotient.mk (genericIdeal D)
    (SexticMumford.xClass Model X)

def goodYbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  Ideal.Quotient.mk (genericIdeal D)
    (N13GoodSexticCoordinateEquiv.goodYInSextic (K := Q₂))

/-- The inverse affine coordinate inside the generic graph quotient. -/
def tbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  algebraMap Q₂ (GenericQuotient D) (-(D.u.coeff 0)⁻¹) *
    (xbar D +
      algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))

/-- The ordinary infinity ordinate inside the generic graph quotient. -/
def vbar
    (D : SexticMumford.Mumford Model) :
    GenericQuotient D :=
  tbar D ^ 3 * goodYbar D

theorem xbar_quadratic
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    xbar D ^ 2 +
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) *
          xbar D +
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) = 0 := by
  have hu :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model D.u) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (SexticMumford.xClass_mem_mumfordIdeal
        Model D.toSemi.u D.toSemi.v)
  have hshape :=
    N13IrreducibleQuadraticChart.monic_quadratic_eq
      D.u D.u_monic hdeg
  have hxshape :
      SexticMumford.xClass Model D.u =
        SexticMumford.xClass Model X ^ 2 +
          SexticMumford.xClass Model (C (D.u.coeff 1)) *
            SexticMumford.xClass Model X +
          SexticMumford.xClass Model (C (D.u.coeff 0)) := by
    rw [hshape]
    simp [SexticMumford.xClass, SexticMumford.mk]
  rw [hxshape] at hu
  simp only [map_add, map_mul, map_pow] at hu
  have hC (c : Q₂) :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model (C c)) =
        algebraMap Q₂ (GenericQuotient D) c := by
    rfl
  rw [hC, hC] at hu
  simpa only [xbar] using hu

theorem xbar_mul_tbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    xbar D * tbar D = 1 := by
  have hu := xbar_quadratic D hdeg
  let u0 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)
  let u0i : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹)
  have hunit : u0i * u0 = 1 := by
    dsimp only [u0i, u0]
    rw [← map_mul]
    simp [h0]
  dsimp only [tbar]
  rw [map_neg]
  change
    xbar D *
        (-u0i *
          (xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))) =
      1
  linear_combination -u0i * hu + hunit

theorem xbar_eq_linear_tbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    xbar D =
      algebraMap Q₂ (GenericQuotient D) (-D.u.coeff 0) *
          tbar D -
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
  have hu :
      algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) *
          algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹) =
        1 := by
    rw [← map_mul]
    simp [h0]
  dsimp only [tbar]
  rw [map_neg, map_neg]
  calc
    xbar D =
        (algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) *
            algebraMap Q₂ (GenericQuotient D)
              ((D.u.coeff 0)⁻¹)) *
          (xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1)) -
          algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
            rw [hu]
            ring
    _ =
        (-algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)) *
            (-algebraMap Q₂ (GenericQuotient D)
                ((D.u.coeff 0)⁻¹) *
              (xbar D +
                algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))) -
          algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) := by
            ring

theorem goodYInSextic_relation :
    N13GoodSexticCoordinateEquiv.goodYInSextic (K := Q₂) ^ 2 +
        SexticMumford.xClass Model
            (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) *
          N13GoodSexticCoordinateEquiv.goodYInSextic (K := Q₂) =
      SexticMumford.xClass Model
        (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂)) := by
  have h :=
    congrArg
      (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
      (N13GeneralizedMumfordIntegral.yClass_relation (R := Q₂))
  simpa only [map_add, map_mul, map_pow,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass] using h

theorem goodYbar_relation
    (D : SexticMumford.Mumford Model) :
    goodYbar D ^ 2 +
        (xbar D ^ 3 + xbar D + 1) * goodYbar D =
      xbar D ^ 5 + xbar D ^ 4 := by
  have h :=
    congrArg (Ideal.Quotient.mk (genericIdeal D))
      goodYInSextic_relation
  simpa [goodYbar, xbar,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using h

theorem vbar_relation
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    vbar D ^ 2 +
        (1 + tbar D ^ 2 + tbar D ^ 3) * vbar D =
      tbar D + tbar D ^ 2 := by
  exact
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      (xbar D) (tbar D) (goodYbar D)
      (xbar_mul_tbar D hdeg h0)
      (goodYbar_relation D)

def coefficientToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    R₂ →+* GenericQuotient D :=
  (algebraMap Q₂ (GenericQuotient D)).comp
    N13TwoAdicCoordinateBaseChange.coeffMap

def baseToGenericQuotient
    (D : SexticMumford.Mumford Model) :
    R₂[X] →+* GenericQuotient D :=
  Polynomial.eval₂RingHom
    (coefficientToGenericQuotient D) (tbar D)

private theorem infinityCurve_root
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        (baseToGenericQuotient D) (vbar D) = 0 := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul, sub_eq_zero]
  simpa [baseToGenericQuotient, coefficientToGenericQuotient,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] using
      vbar_relation D hdeg h0

def integralInfinityToGenericQuotient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityRing →+* GenericQuotient D :=
  AdjoinRoot.lift
    (baseToGenericQuotient D)
    (vbar D)
    (infinityCurve_root D hdeg h0)

@[simp] theorem integralInfinityToGenericQuotient_tClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    integralInfinityToGenericQuotient D hdeg h0
        N13IntegralInfinityChart.tClass = tbar D := by
  simp [integralInfinityToGenericQuotient,
    N13IntegralInfinityChart.tClass, baseToGenericQuotient]

@[simp] theorem integralInfinityToGenericQuotient_vClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    integralInfinityToGenericQuotient D hdeg h0
        N13IntegralInfinityChart.vClass = vbar D :=
  AdjoinRoot.lift_root (infinityCurve_root D hdeg h0)

/-- The canonical integral infinity ideal attached directly to the generic
Mumford graph quotient. -/
def integralInfinityIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Ideal InfinityRing :=
  RingHom.ker (integralInfinityToGenericQuotient D hdeg h0)

def genericQuotientMap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityRing ⧸ integralInfinityIdeal D hdeg h0 →+*
      GenericQuotient D :=
  Ideal.Quotient.lift
    (integralInfinityIdeal D hdeg h0)
    (integralInfinityToGenericQuotient D hdeg h0)
    (by
      intro a ha
      exact ha)

@[simp] theorem genericQuotientMap_mk
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (z : InfinityRing) :
    genericQuotientMap D hdeg h0
        (Ideal.Quotient.mk
          (integralInfinityIdeal D hdeg h0) z) =
      integralInfinityToGenericQuotient D hdeg h0 z :=
  Ideal.Quotient.lift_mk _ _ _

theorem genericQuotientMap_injective
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Function.Injective (genericQuotientMap D hdeg h0) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change integralInfinityToGenericQuotient D hdeg h0 a = 0
  calc
    integralInfinityToGenericQuotient D hdeg h0 a =
        genericQuotientMap D hdeg h0
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0) a) :=
      (genericQuotientMap_mk D hdeg h0 a).symm
    _ = genericQuotientMap D hdeg h0 (z - w) :=
      congrArg (genericQuotientMap D hdeg h0) ha
    _ = 0 := by rw [map_sub, hzw, sub_self]

@[simp] theorem integralInfinityToGenericQuotient_xClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (p : R₂[X]) :
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      baseToGenericQuotient D p := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) = _
  exact AdjoinRoot.lift_of (infinityCurve_root D hdeg h0)

@[simp] theorem integralInfinityToGenericQuotient_algebraMap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (r : R₂) :
    integralInfinityToGenericQuotient D hdeg h0
        (algebraMap R₂ InfinityRing r) =
      algebraMap Q₂ (GenericQuotient D)
        (N13TwoAdicCoordinateBaseChange.coeffMap r) := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom (C r)) = _
  rw [integralInfinityToGenericQuotient_xClass]
  simp [baseToGenericQuotient, coefficientToGenericQuotient]

theorem baseToGenericQuotient_eq_aeval_mapPoly
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    baseToGenericQuotient D p =
      aeval (tbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) := by
  change
    p.eval₂
        ((algebraMap Q₂ (GenericQuotient D)).comp
          N13TwoAdicCoordinateBaseChange.coeffMap)
        (tbar D) =
      (p.map N13TwoAdicCoordinateBaseChange.coeffMap).eval₂
        (algebraMap Q₂ (GenericQuotient D)) (tbar D)
  exact
    (Polynomial.eval₂_map
      (p := p)
      N13TwoAdicCoordinateBaseChange.coeffMap
      (algebraMap Q₂ (GenericQuotient D))
      (tbar D)).symm

theorem reciprocal_aeval_tbar_eq_zero
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    aeval (tbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly
          (N13ReciprocalQuadraticReflection.integralReciprocal a b)) =
      0 := by
  have hu := xbar_quadratic D hdeg
  have htx : tbar D * xbar D = 1 := by
    simpa [mul_comm] using xbar_mul_tbar D hdeg h0
  let u0 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)
  let u0i : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹)
  let u1 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1)
  have hunit : u0i * u0 = 1 := by
    dsimp only [u0i, u0]
    rw [← map_mul]
    simp [h0]
  have hmapm :
      N13TwoAdicCoordinateBaseChange.mapPoly
          (N13ReciprocalQuadraticReflection.integralReciprocal a b) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹) := by
    simpa [N13ReciprocalQuadraticReflection.integralReciprocal,
      N13TwoAdicCoordinateBaseChange.mapPoly,
      N13TwoAdicCoordinateBaseChange.coeffMap,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap] using hm
  rw [hmapm]
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  change
    tbar D ^ 2 +
        (algebraMap Q₂ (GenericQuotient D)
          (D.u.coeff 1 / D.u.coeff 0)) * tbar D +
        u0i = 0
  rw [div_eq_mul_inv, map_mul]
  change tbar D ^ 2 + u1 * u0i * tbar D + u0i = 0
  calc
    tbar D ^ 2 + u1 * u0i * tbar D + u0i =
        u0i * tbar D ^ 2 *
          (xbar D ^ 2 + u1 * xbar D + u0) := by
      calc
        _ =
            u0i * (tbar D * xbar D) ^ 2 +
              u0i * u1 * tbar D * (tbar D * xbar D) +
              (u0i * u0) * tbar D ^ 2 := by
                rw [htx, hunit]
                ring
        _ = _ := by ring
    _ = 0 := by
      change
        u0i * tbar D ^ 2 *
          (xbar D ^ 2 +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) *
              xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)) = 0
      simpa [hu]

theorem reciprocal_mem_integralInfinityIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    N13IntegralInfinityGraphJacobian.xClassHom
        (N13ReciprocalQuadraticReflection.integralReciprocal a b) ∈
      integralInfinityIdeal D hdeg h0 := by
  rw [integralInfinityIdeal, RingHom.mem_ker]
  rw [integralInfinityToGenericQuotient_xClass]
  rw [baseToGenericQuotient_eq_aeval_mapPoly]
  exact reciprocal_aeval_tbar_eq_zero D hdeg h0 a b hm

theorem aeval_tClass
    (p : R₂[X]) :
    aeval N13IntegralInfinityChart.tClass p =
      N13IntegralInfinityReduction.integralBaseClass p := by
  let ψ : R₂[X] →ₐ[R₂] InfinityRing :=
    IsScalarTower.toAlgHom R₂ R₂[X] InfinityRing
  have h :
      aeval N13IntegralInfinityChart.tClass = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun h p

theorem infinity_rankTwoPolynomialNormalForm :
    ∀ z : InfinityRing,
      ∃ P Q : R₂[X],
        z =
          aeval N13IntegralInfinityChart.tClass P +
            aeval N13IntegralInfinityChart.tClass Q *
              N13IntegralInfinityChart.vClass := by
  intro z
  refine
    ⟨N13IntegralInfinityReduction.integralCoeff0 z,
      N13IntegralInfinityReduction.integralCoeffV z, ?_⟩
  rw [aeval_tClass, aeval_tClass]
  exact (N13IntegralInfinityReduction.integral_recompose z).symm

theorem integralInfinityQuotient_finite
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    Module.Finite R₂
      (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) := by
  apply
    N13QuotientFiniteness.quotient_finite_of_monic_relation_of_rankTwoNormalForm
        N13IntegralInfinityChart.tClass
        N13IntegralInfinityChart.vClass
        infinity_rankTwoPolynomialNormalForm
        (integralInfinityIdeal D hdeg h0)
        (N13ReciprocalQuadraticReflection.integralReciprocal_monic
          a b)
  rw [aeval_tClass]
  exact reciprocal_mem_integralInfinityIdeal D hdeg h0 a b hm

theorem integralInfinityIdeal_scalarSaturated
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    ∀ (r : R₂), r ≠ 0 → ∀ z : InfinityRing,
      algebraMap R₂ InfinityRing r * z ∈
          integralInfinityIdeal D hdeg h0 →
        z ∈ integralInfinityIdeal D hdeg h0 := by
  intro r hr z hz
  rw [integralInfinityIdeal, RingHom.mem_ker] at hz ⊢
  rw [map_mul, integralInfinityToGenericQuotient_algebraMap] at hz
  have hrQ :
      N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
    exact
      (IsFractionRing.injective R₂ Q₂).ne hr
  have hsunit :
      IsUnit
        (algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
    (isUnit_iff_ne_zero.mpr hrQ).map
      (algebraMap Q₂ (GenericQuotient D))
  let u : (GenericQuotient D)ˣ :=
    hsunit.unit
  have hu :
      (u : GenericQuotient D) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r) :=
    hsunit.unit_spec
  calc
    integralInfinityToGenericQuotient D hdeg h0 z =
        ((u⁻¹ : (GenericQuotient D)ˣ) : GenericQuotient D) *
          ((u : GenericQuotient D) *
            integralInfinityToGenericQuotient D hdeg h0 z) := by
              simp
    _ = 0 := by rw [hu, hz, mul_zero]

theorem integralInfinityQuotient_isTorsionFree
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Module.IsTorsionFree R₂
      (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) :=
  N13QuotientVerticalFlatness.quotient_isTorsionFree_of_scalar_saturated
      (integralInfinityIdeal D hdeg h0)
      (integralInfinityIdeal_scalarSaturated D hdeg h0)

theorem integralInfinityQuotient_flat
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Module.Flat R₂
      (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) := by
  letI :
      Module.IsTorsionFree R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) :=
    integralInfinityQuotient_isTorsionFree D hdeg h0
  infer_instance

theorem exists_genericQuotient_basis_oneT
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    ∃ bT : Basis (Fin 2) Q₂ (GenericQuotient D),
      (bT : Fin 2 → GenericQuotient D) =
        N13FiniteFlatBasisLift.oneX (tbar D) := by
  let bX :=
    SexticMumfordQuotientBasis.quotientBasis
      Model D.toSemi hdeg
  have hbX :
      (bX : Fin 2 → GenericQuotient D) =
        N13FiniteFlatBasisLift.oneX (xbar D) := by
    funext i
    fin_cases i
    · change bX (0 : Fin 2) = 1
      exact
        SexticMumfordQuotientBasis.quotientBasis_zero
          Model D.toSemi hdeg
    · change
        bX (1 : Fin 2) =
          Ideal.Quotient.mk
            (SexticMumford.mumfordIdeal
              Model D.toSemi.u D.toSemi.v)
            (SexticMumford.xClass Model X)
      exact
        SexticMumfordQuotientBasis.quotientBasis_one
          Model D.toSemi hdeg
  have hone : (1 : GenericQuotient D) ≠ 0 := by
    have hbX0 :
        bX (0 : Fin 2) = 1 :=
      SexticMumfordQuotientBasis.quotientBasis_zero
        Model D.toSemi hdeg
    intro h
    exact bX.ne_zero 0 (hbX0.trans h)
  have hliX :
      LinearIndependent Q₂
        (N13FiniteFlatBasisLift.oneX (xbar D)) := by
    rw [← hbX]
    exact bX.linearIndependent
  have hliT :
      LinearIndependent Q₂
        (N13FiniteFlatBasisLift.oneX (tbar D)) := by
    rw [show N13FiniteFlatBasisLift.oneX (tbar D) =
        ![1, tbar D] by rfl,
      LinearIndependent.pair_iff' hone]
    intro α hα
    have hxscalar :
        algebraMap Q₂ (GenericQuotient D)
            (-D.u.coeff 0 * α - D.u.coeff 1) =
          xbar D := by
      rw [xbar_eq_linear_tbar D hdeg h0, ← hα]
      simp only [map_sub, map_mul, map_neg, Algebra.smul_def,
        mul_one]
    have hnon :=
      (LinearIndependent.pair_iff' hone).mp
        (by
          simpa [N13FiniteFlatBasisLift.oneX] using hliX)
    exact
      hnon (-D.u.coeff 0 * α - D.u.coeff 1)
        (by simpa [Algebra.smul_def] using hxscalar)
  have hfin :
      Module.finrank Q₂ (GenericQuotient D) = 2 := by
    exact Module.finrank_eq_card_basis bX
  let bT : Basis (Fin 2) Q₂ (GenericQuotient D) :=
    basisOfLinearIndependentOfCardEqFinrank
      hliT (by simp [hfin])
  exact ⟨bT, by simp [bT]⟩

def genericQuotientAlgHom
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) →ₐ[R₂]
      GenericQuotient D where
  toRingHom := genericQuotientMap D hdeg h0
  commutes' r := by
    change
      integralInfinityToGenericQuotient D hdeg h0
          (algebraMap R₂ InfinityRing r) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)
    exact integralInfinityToGenericQuotient_algebraMap D hdeg h0 r

theorem integralInfinityQuotient_finrank_eq_two
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0)) :
    Module.finrank R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
      2 := by
  let Iinf := integralInfinityIdeal D hdeg h0
  let B := InfinityRing ⧸ Iinf
  let G := GenericQuotient D
  let q : B →+* G := genericQuotientMap D hdeg h0
  let qAlg : B →ₐ[R₂] G :=
    genericQuotientAlgHom D hdeg h0
  change Module.finrank R₂ B = 2
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    integralInfinityQuotient_flat D hdeg h0
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨bT, hbT⟩ :=
    exists_genericQuotient_basis_oneT D hdeg h0
  letI : Module.Finite Q₂ G :=
    Module.Finite.of_basis bT
  have hq : Function.Injective q :=
    genericQuotientMap_injective D hdeg h0
  have hfactor :
      q.comp (algebraMap R₂ B) = algebraMap R₂ G := by
    ext r
    change
      integralInfinityToGenericQuotient D hdeg h0
          (algebraMap R₂ InfinityRing r) =
        algebraMap Q₂ (GenericQuotient D)
          (N13TwoAdicCoordinateBaseChange.coeffMap r)
    exact integralInfinityToGenericQuotient_algebraMap D hdeg h0 r
  have hli :
      LinearIndependent R₂
        (N13TwoFiberNoEscape.pairFamily
          (1 : B)
          (Ideal.Quotient.mk Iinf
            N13IntegralInfinityChart.tClass)) := by
    apply
      N13TwoFiberNoEscape.pair_linearIndependent_of_fraction_basis
        (R := R₂) (K := Q₂)
        q hfactor hq
        1
        (Ideal.Quotient.mk Iinf
          N13IntegralInfinityChart.tClass)
        bT
    · simpa [q, hbT, N13FiniteFlatBasisLift.oneX]
    · change
        genericQuotientMap D hdeg h0
            (Ideal.Quotient.mk
              (integralInfinityIdeal D hdeg h0)
              N13IntegralInfinityChart.tClass) =
          bT 1
      rw [genericQuotientMap_mk,
        integralInfinityToGenericQuotient_tClass]
      simpa [N13FiniteFlatBasisLift.oneX] using
        (congrFun hbT (1 : Fin 2)).symm
  have hlo : 2 ≤ Module.finrank R₂ B := by
    simpa using hli.fintype_card_le_finrank
  have hrank :
      Module.rank Q₂ G = Module.rank R₂ G :=
    IsLocalization.rank_eq Q₂ (nonZeroDivisors R₂) le_rfl
  have hGfinite : Module.rank R₂ G < Cardinal.aleph0 := by
    rw [← hrank]
    exact Module.rank_lt_aleph0 Q₂ G
  have hhi : Module.finrank R₂ B ≤ Module.finrank R₂ G :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_injective
        qAlg.toLinearMap hq)
      hGfinite
  have hfield :
      Module.finrank Q₂ G = Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hGtwo : Module.finrank R₂ G = 2 := by
    rw [← hfield, Module.finrank_eq_card_basis bT]
    rfl
  rw [hGtwo] at hhi
  omega

private theorem specialInfinity_coordinate_adjoin_eq_top :
    Algebra.adjoin k
        ({N13SpecialInfinityChart.tClass,
          N13SpecialInfinityChart.vClass} : Set SpecialRing) =
      ⊤ := by
  let S : Subalgebra k SpecialRing :=
    Algebra.adjoin k
      ({N13SpecialInfinityChart.tClass,
        N13SpecialInfinityChart.vClass} : Set SpecialRing)
  have hbase (p : k[X]) :
      algebraMap k[X] SpecialRing p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        exact
          S.mul_mem (S.algebraMap_mem a)
            (S.pow_mem
              (Algebra.subset_adjoin
                (Set.mem_insert
                  N13SpecialInfinityChart.tClass
                  {N13SpecialInfinityChart.vClass})) n)
  apply Algebra.eq_top_iff.2
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk N13SpecialInfinityChart.curvePoly p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact
        S.mul_mem (hbase a)
          (S.pow_mem
            (Algebra.subset_adjoin
              (Set.mem_insert_iff.mpr
                (Or.inr
                  (Set.mem_singleton
                    N13SpecialInfinityChart.vClass)))) n)

private theorem specialInfinity_quotient_coordinate_adjoin_eq_top
    (J : Ideal SpecialRing) :
    Algebra.adjoin k
        ({Ideal.Quotient.mk J N13SpecialInfinityChart.tClass,
          Ideal.Quotient.mk J N13SpecialInfinityChart.vClass} :
          Set (SpecialRing ⧸ J)) =
      ⊤ := by
  let π : SpecialRing →ₐ[k] SpecialRing ⧸ J :=
    Ideal.Quotient.mkₐ k J
  rw [show
      ({Ideal.Quotient.mk J N13SpecialInfinityChart.tClass,
        Ideal.Quotient.mk J N13SpecialInfinityChart.vClass} :
        Set (SpecialRing ⧸ J)) =
        π ''
          ({N13SpecialInfinityChart.tClass,
            N13SpecialInfinityChart.vClass} :
            Set SpecialRing) by
      exact (Set.image_pair π _ _).symm]
  rw [← AlgHom.map_adjoin,
    specialInfinity_coordinate_adjoin_eq_top,
    Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

def reduceInfinityQuotient
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    InfinityRing ⧸ I →+* SpecialRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13IntegralInfinityReduction.reduceCoordinate I J hmap

@[simp] theorem reduceInfinityQuotient_mk
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J)
    (z : InfinityRing) :
    reduceInfinityQuotient I J hmap (Ideal.Quotient.mk I z) =
      Ideal.Quotient.mk J
        (N13IntegralInfinityReduction.reduceCoordinate z) :=
  rfl

theorem reduceInfinityQuotient_surjective
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    Function.Surjective (reduceInfinityQuotient I J hmap) :=
  N13QuotientReduction.inducedQuotientMap_surjective
    N13IntegralInfinityReduction.reduceCoordinate
    N13IntegralInfinityReduction.reduceCoordinate_surjective
    I J hmap

theorem ker_reduceInfinityQuotient_eq_span_two
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceInfinityQuotient I J hmap) =
      Ideal.span
        ({algebraMap R₂ (InfinityRing ⧸ I) (2 : R₂)} :
          Set (InfinityRing ⧸ I)) := by
  simpa only [reduceInfinityQuotient,
    Ideal.Quotient.mk_algebraMap] using
    (N13QuotientReduction.ker_inducedQuotientMap_eq_span
      N13IntegralInfinityReduction.reduceCoordinate
      N13IntegralInfinityReduction.reduceCoordinate_surjective
      I J hmap
      (algebraMap R₂ InfinityRing (2 : R₂))
      N13IntegralInfinityReduction.ker_reduceCoordinate)

theorem specialQuotientMap_comp_algebraMap
    (I : Ideal InfinityRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate I =
        J) :
    (reduceInfinityQuotient I J hmap).comp
        (algebraMap R₂ (InfinityRing ⧸ I)) =
      (algebraMap k (SpecialRing ⧸ J)).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13IntegralInfinityReduction.reduceCoordinate
          (algebraMap R₂ InfinityRing r)) =
      Ideal.Quotient.mk J
        (algebraMap k SpecialRing
          (N13IntegralInfinityReduction.reduceBase r))
  congr 1
  change
    N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityReduction.integralBaseClass (C r)) =
      N13IntegralInfinityReduction.specialBaseClass
        (C (N13IntegralInfinityReduction.reduceBase r))
  rw [N13IntegralInfinityReduction.reduce_integralBaseClass]
  simp [N13IntegralInfinityReduction.reducePoly]

theorem exists_integralInfinity_basis_oneT_or_oneV
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0)) :
    (∃ bT : Basis (Fin 2) R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0),
      (bT : Fin 2 →
        InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0)
            N13IntegralInfinityChart.tClass)) ∨
      (∃ bV : Basis (Fin 2) R₂
        (InfinityRing ⧸ integralInfinityIdeal D hdeg h0),
      (bV : Fin 2 →
        InfinityRing ⧸ integralInfinityIdeal D hdeg h0) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (integralInfinityIdeal D hdeg h0)
            N13IntegralInfinityChart.vClass)) := by
  let I := integralInfinityIdeal D hdeg h0
  let J : Ideal SpecialRing :=
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate I
  let B := InfinityRing ⧸ I
  let C := SpecialRing ⧸ J
  let g : B →+* C :=
    reduceInfinityQuotient I J rfl
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    integralInfinityQuotient_flat D hdeg h0
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  letI : IsScalarTower R₂ k C :=
    IsScalarTower.of_algebraMap_eq
      (R := R₂) (S := k) (A := C) fun _ => rfl
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap k C).comp (algebraMap R₂ k) := by
    exact specialQuotientMap_comp_algebraMap I J rfl
  have hg : Function.Surjective g :=
    reduceInfinityQuotient_surjective I J rfl
  have hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    ker_reduceInfinityQuotient_eq_span_two I J rfl
  let eK : k ⊗[R₂] B ≃ₗ[k] C :=
    N13TensorSpecialFiber.tensorLinearEquiv
      (g := g)
      (hfactor := hfactor)
      (hq := ZMod.ringHom_surjective PadicInt.toZMod)
      (π := (2 : R₂))
      (hπ := N13IntegralInfinityReduction.reduceBase_two)
      (hg := hg)
      (hker := hker)
  have hfinB : Module.finrank R₂ B = 2 :=
    integralInfinityQuotient_finrank_eq_two
      D hdeg h0 hfinite
  have hfinC : Module.finrank k C = 2 := by
    rw [← eK.finrank_eq, Module.finrank_baseChange, hfinB]
  letI : Nontrivial C :=
    Module.nontrivial_of_finrank_pos
      (R := k) (M := C) (by rw [hfinC]; decide)
  let tB : B :=
    Ideal.Quotient.mk I N13IntegralInfinityChart.tClass
  let vB : B :=
    Ideal.Quotient.mk I N13IntegralInfinityChart.vClass
  let tC : C :=
    Ideal.Quotient.mk J N13SpecialInfinityChart.tClass
  let vC : C :=
    Ideal.Quotient.mk J N13SpecialInfinityChart.vClass
  have hgen :
      Algebra.adjoin k ({tC, vC} : Set C) = ⊤ :=
    specialInfinity_quotient_coordinate_adjoin_eq_top J
  have hexC :=
    N13TwoGeneratorFiberBasis.exists_basis_oneX_or_oneY
      tC vC hfinC hgen
  have hfactorκ :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ C).comp (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k C (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R₂ C r :=
        (IsScalarTower.algebraMap_apply R₂ k C r).symm
      _ = algebraMap κ C (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply R₂ κ C r
      _ = algebraMap κ C
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let eκ : κ ⊗[R₂] B ≃ₗ[κ] C :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactorκ (2 : R₂) htwo hg hker
  have eκ_tmul_one (z : B) :
      eκ (TensorProduct.mk R₂ κ B 1 z) = g z := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactorκ (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] z) = g z
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactorκ)
        (π := (2 : R₂))
        (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) z)
  have hκk :
      Function.Surjective (algebraMap κ k) := by
    intro a
    obtain ⟨r, hr⟩ :=
      ZMod.ringHom_surjective PadicInt.toZMod a
    refine ⟨IsLocalRing.residue R₂ r, ?_⟩
    calc
      algebraMap κ k (IsLocalRing.residue R₂ r) =
          algebraMap R₂ k r := by
        exact
          (IsScalarTower.algebraMap_apply R₂ κ k r).symm
      _ = a := hr
  have ht_map : g tB = tC := by
    change
      reduceInfinityQuotient I J rfl
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass) =
        tC
    rw [reduceInfinityQuotient_mk,
      N13IntegralInfinityReduction.reduce_tClass]
  have hv_map : g vB = vC := by
    change
      reduceInfinityQuotient I J rfl
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.vClass) =
        vC
    rw [reduceInfinityQuotient_mk,
      N13IntegralInfinityReduction.reduce_vClass]
  rcases hexC with ⟨bC, hbC⟩ | ⟨bC, hbC⟩
  · left
    obtain ⟨bCκ, hbCκ⟩ :=
      N13ContractQuotientXYBasis.exists_basis_restrictScalars_of_surjective
        hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX tB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ht_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX tB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX tB) bCκ heval i
    simpa [I, B, tB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) tB b₀ hb₀
  · right
    obtain ⟨bCκ, hbCκ⟩ :=
      N13ContractQuotientXYBasis.exists_basis_restrictScalars_of_surjective
        hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX vB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, hv_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX vB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX vB) bCκ heval i
    simpa [I, B, vB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) vB b₀ hb₀

theorem quotient_aeval_tClass
    (I : Ideal InfinityRing)
    (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13IntegralInfinityChart.tClass) p =
      Ideal.Quotient.mk I
        (N13IntegralInfinityGraphJacobian.xClassHom p) := by
  calc
    aeval
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass) p =
        Ideal.Quotient.mk I
          (aeval N13IntegralInfinityChart.tClass p) := by
      simpa using
        (Polynomial.map_aeval_eq_aeval_map
          (R := R₂) (S := InfinityRing) (T := R₂)
          (U := InfinityRing ⧸ I)
          (φ := RingHom.id R₂)
          (ψ := Ideal.Quotient.mk I)
          (by ext; simp) p
          N13IntegralInfinityChart.tClass).symm
    _ =
        Ideal.Quotient.mk I
          (N13IntegralInfinityGraphJacobian.xClassHom p) := by
      rw [N13RankTwoInfinityVerticalGraphRecovery.aeval_tClass]
      rfl

theorem graphData_u_eq_of_basis
    (I : Ideal InfinityRing)
    (bI : Basis (Fin 2) R₂ (InfinityRing ⧸ I))
    (hbI :
      (bI : Fin 2 → InfinityRing ⧸ I) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass))
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hEMonic : E.u.Monic)
    (hEDegree : E.u.natDegree = 2)
    (hI :
      I = N13IntegralInfinityGraphTwoChart.infinityIdeal E)
    (m : R₂[X])
    (hmMonic : m.Monic)
    (hmDegree : m.natDegree = 2)
    (hmI :
      N13IntegralInfinityGraphJacobian.xClassHom m ∈ I) :
    E.u = m := by
  let tI : InfinityRing ⧸ I :=
    Ideal.Quotient.mk I N13IntegralInfinityChart.tClass
  have hb0 : bI 0 = 1 := by
    have h := congrFun hbI (0 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX] using h
  have hb1 : bI 1 = tI := by
    have h := congrFun hbI (1 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX, tI] using h
  letI : Module.Free R₂ (InfinityRing ⧸ I) :=
    Module.Free.of_basis bI
  letI : Module.Finite R₂ (InfinityRing ⧸ I) :=
    Module.Finite.of_basis bI
  letI : Nontrivial (InfinityRing ⧸ I) :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact bI.ne_zero 0⟩⟩
  let u : R₂[X] :=
    (Algebra.lmul R₂ (InfinityRing ⧸ I) tI).charpoly
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x tI
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      tI bI hb0 hb1
  have hker :
      RingHom.ker
          ((aeval tI : R₂[X] →ₐ[R₂]
            InfinityRing ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) :=
    N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
      tI bI hb0 hb1
  have hEuI :
      N13IntegralInfinityGraphJacobian.xClassHom E.u ∈ I := by
    rw [hI]
    exact
      GeneralizedGraphIdealCore.xClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass E.u E.v
  have hEuEval : aeval tI E.u = 0 := by
    rw [quotient_aeval_tClass]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hEuI
  have hEuDvd : u ∣ E.u := by
    have hmem :
        E.u ∈
          RingHom.ker
            ((aeval tI : R₂[X] →ₐ[R₂]
              InfinityRing ⧸ I).toRingHom) :=
      RingHom.mem_ker.mpr hEuEval
    rw [hker, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hmEval : aeval tI m = 0 := by
    rw [quotient_aeval_tClass]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmI
  have hmDvd : u ∣ m := by
    have hmem :
        m ∈
          RingHom.ker
            ((aeval tI : R₂[X] →ₐ[R₂]
              InfinityRing ⧸ I).toRingHom) :=
      RingHom.mem_ker.mpr hmEval
    rw [hker, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hEu :
      E.u = u :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      huMonic hEMonic hEuDvd
      (by rw [hEDegree, huDegree])
  have hm :
      m = u :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      huMonic hmMonic hmDvd
      (by rw [hmDegree, huDegree])
  exact hEu.trans hm.symm

theorem aeval_mapPoly_xbar
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    aeval (xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) =
      p.eval₂ (coefficientToGenericQuotient D) (xbar D) := by
  change
    (p.map N13TwoAdicCoordinateBaseChange.coeffMap).eval₂
        (algebraMap Q₂ (GenericQuotient D)) (xbar D) =
      p.eval₂
        ((algebraMap Q₂ (GenericQuotient D)).comp
          N13TwoAdicCoordinateBaseChange.coeffMap)
        (xbar D)
  exact
    Polynomial.eval₂_map
      (p := p)
      N13TwoAdicCoordinateBaseChange.coeffMap
      (algebraMap Q₂ (GenericQuotient D))
      (xbar D)

theorem aeval_xbar
    (D : SexticMumford.Mumford Model)
    (p : Q₂[X]) :
    aeval (xbar D) p =
      Ideal.Quotient.mk (genericIdeal D)
        (SexticMumford.xClass Model p) := by
  let ψ : Q₂[X] →ₐ[Q₂] GenericQuotient D :=
    IsScalarTower.toAlgHom Q₂ Q₂[X] (GenericQuotient D)
  have h :
      aeval (xbar D) = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun h p

theorem aeval_mapPoly_reflect_xbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (n : ℕ)
    (p : R₂[X])
    (hp : p.natDegree ≤ n) :
    aeval (xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly
          (p.reflect n)) =
      xbar D ^ n * baseToGenericQuotient D p := by
  have htx : tbar D * xbar D = 1 := by
    simpa [mul_comm] using xbar_mul_tbar D hdeg h0
  have htunit : IsUnit (tbar D) :=
    isUnit_iff_exists_inv.mpr ⟨xbar D, htx⟩
  letI : Invertible (tbar D) :=
    htunit.invertible
  have hinv : ⅟(tbar D) = xbar D :=
    invOf_eq_right_inv htx
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      (coefficientToGenericQuotient D)
      (tbar D) n p hp
  rw [hinv] at hreflect
  rw [aeval_mapPoly_xbar]
  change
    (p.reflect n).eval₂
          (coefficientToGenericQuotient D) (xbar D) =
      xbar D ^ n *
        p.eval₂ (coefficientToGenericQuotient D) (tbar D)
  calc
    (p.reflect n).eval₂
          (coefficientToGenericQuotient D) (xbar D) =
        1 *
          ((p.reflect n).eval₂
            (coefficientToGenericQuotient D) (xbar D)) := by
              simp
    _ =
        (xbar D ^ n * tbar D ^ n) *
          ((p.reflect n).eval₂
            (coefficientToGenericQuotient D) (xbar D)) := by
          rw [← mul_pow, xbar_mul_tbar D hdeg h0,
            one_pow, one_mul]
    _ =
        xbar D ^ n *
          (((p.reflect n).eval₂
              (coefficientToGenericQuotient D) (xbar D)) *
            tbar D ^ n) := by ring
    _ =
        xbar D ^ n *
          p.eval₂ (coefficientToGenericQuotient D) (tbar D) := by
            rw [hreflect]

theorem vbar_eq_baseToGenericQuotient_of_graphIdeal_eq
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hI :
      integralInfinityIdeal D hdeg h0 =
        N13IntegralInfinityGraphTwoChart.infinityIdeal E) :
    vbar D = baseToGenericQuotient D E.v := by
  have hmem :
      GeneralizedGraphIdealCore.ySubClass
          N13IntegralInfinityGraphJacobian.xClassHom
          N13IntegralInfinityGraphJacobian.yClass E.v ∈
        integralInfinityIdeal D hdeg h0 := by
    rw [hI]
    exact
      GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass E.u E.v
  rw [integralInfinityIdeal, RingHom.mem_ker] at hmem
  change
    integralInfinityToGenericQuotient D hdeg h0
      (N13IntegralInfinityChart.vClass -
        N13IntegralInfinityGraphJacobian.xClassHom E.v) = 0 at hmem
  rw [map_sub, integralInfinityToGenericQuotient_vClass,
    integralInfinityToGenericQuotient_xClass] at hmem
  exact sub_eq_zero.mp hmem

theorem recovered_affineV_aeval_eq_goodYbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hvDegree : E.v.natDegree ≤ 3)
    (hI :
      integralInfinityIdeal D hdeg h0 =
        N13IntegralInfinityGraphTwoChart.infinityIdeal E) :
    aeval (xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly
          (N13IntegralInfinityGraphTwoChart.affineV E)) =
      goodYbar D := by
  rw [N13IntegralInfinityGraphTwoChart.affineV,
    aeval_mapPoly_reflect_xbar D hdeg h0 3 E.v hvDegree]
  rw [← vbar_eq_baseToGenericQuotient_of_graphIdeal_eq
    D hdeg h0 E hI]
  change xbar D ^ 3 * (tbar D ^ 3 * goodYbar D) = goodYbar D
  rw [← mul_assoc, ← mul_pow, xbar_mul_tbar D hdeg h0,
    one_pow, one_mul]

theorem recovered_generic_ordinate
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hvDegree : E.v.natDegree ≤ 3)
    (hI :
      integralInfinityIdeal D hdeg h0 =
        N13IntegralInfinityGraphTwoChart.infinityIdeal E) :
    D.u ∣
      N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly
            (N13IntegralInfinityGraphTwoChart.affineV E)) -
        D.v := by
  let V : Q₂[X] :=
    N13GoodSexticMumfordTransport.completedGraph
      (N13TwoAdicCoordinateBaseChange.mapPoly
        (N13IntegralInfinityGraphTwoChart.affineV E))
  have hVeval :
      aeval (xbar D) V =
        Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.yClass Model) := by
    rw [show V =
        2 *
            N13TwoAdicCoordinateBaseChange.mapPoly
              (N13IntegralInfinityGraphTwoChart.affineV E) +
          N13GeneralizedMumfordIntegral.hPoly by
      rfl,
      map_add, map_mul, map_ofNat,
      recovered_affineV_aeval_eq_goodYbar
        D hdeg h0 E hvDegree hI]
    rw [aeval_xbar]
    let c : GenericQuotient D :=
      algebraMap Q₂ (GenericQuotient D) (2 : Q₂)⁻¹
    have hc : (2 : GenericQuotient D) * c = 1 := by
      dsimp only [c]
      rw [← map_ofNat (algebraMap Q₂ (GenericQuotient D)) 2,
        ← map_mul]
      norm_num
    simp only [goodYbar,
      N13GoodSexticCoordinateEquiv.goodYInSextic,
      Algebra.smul_def, map_mul, map_sub]
    have hcmap :
        Ideal.Quotient.mk (genericIdeal D)
            (algebraMap Q₂
              (SexticMumford.CoordinateRing Model) (1 / 2)) =
          c := by
      change
        algebraMap Q₂ (GenericQuotient D) (1 / 2) =
          algebraMap Q₂ (GenericQuotient D) (2 : Q₂)⁻¹
      norm_num
    rw [hcmap,
      N13GoodSexticCoordinateEquiv.sexticXHom_apply]
    linear_combination
      (Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.yClass Model) -
        Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model
            N13GeneralizedMumfordIntegral.hPoly)) * hc
  have hyMem :
      SexticMumford.ySubClass Model D.v ∈ genericIdeal D :=
    SexticMumford.ySubClass_mem_mumfordIdeal Model D.u D.v
  have hyZero :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.ySubClass Model D.v) =
        0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hyMem
  have hyEval :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.yClass Model) =
        aeval (xbar D) D.v := by
    apply sub_eq_zero.mp
    rw [aeval_xbar]
    simpa [SexticMumford.ySubClass] using hyZero
  have hzero : aeval (xbar D) (V - D.v) = 0 := by
    rw [map_sub, hVeval, hyEval, sub_self]
  have hzero' :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model (V - D.v)) =
        0 := by
    simpa only [aeval_xbar] using hzero
  have hxMem :
      SexticMumford.xClass Model (V - D.v) ∈ genericIdeal D := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hzero'
  have hxKer :
      SexticMumford.xClass Model (V - D.v) ∈
        RingHom.ker (SexticMumford.mumfordEval Model D.toSemi) := by
    rw [SexticMumford.ker_mumfordEval]
    exact hxMem
  have hxZero := RingHom.mem_ker.mp hxKer
  rw [SexticMumford.mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hxZero
  exact hxZero

theorem exists_horizontal_or_vertical_recovery
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    (∃ E : N13IntegralInfinityGraphTwoChart.GraphData,
      E.u =
        N13ReciprocalQuadraticReflection.integralReciprocal a b ∧
      E.u.Monic ∧
      E.u.natDegree = 2 ∧
      E.v.natDegree ≤ 1 ∧
      E.w.natDegree ≤ 4 ∧
      integralInfinityIdeal D hdeg h0 =
        N13IntegralInfinityGraphTwoChart.infinityIdeal E ∧
      D.u ∣
        N13GoodSexticMumfordTransport.completedGraph
            (N13TwoAdicCoordinateBaseChange.mapPoly
              (N13IntegralInfinityGraphTwoChart.affineV E)) -
          D.v) ∨
      (∃ E :
          N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        integralInfinityIdeal D hdeg h0 = E.ideal) := by
  have hfinite :=
    integralInfinityQuotient_finite D hdeg h0 a b hm
  rcases
      exists_integralInfinity_basis_oneT_or_oneV
        D hdeg h0 hfinite with
    ⟨bT, hbT⟩ | ⟨bV, hbV⟩
  · left
    obtain ⟨E, hEMonic, hEDegree, hvDegree, hwDegree, hI⟩ :=
      N13RankTwoInfinityGraphRecovery.exists_graphData_of_basis
        (integralInfinityIdeal D hdeg h0) bT hbT
    refine
      ⟨E, ?_, hEMonic, hEDegree, hvDegree, hwDegree, hI, ?_⟩
    · exact
        graphData_u_eq_of_basis
        (integralInfinityIdeal D hdeg h0) bT hbT
        E hEMonic hEDegree hI
        (N13ReciprocalQuadraticReflection.integralReciprocal a b)
        (N13ReciprocalQuadraticReflection.integralReciprocal_monic
          a b)
        (N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
          a b)
        (reciprocal_mem_integralInfinityIdeal
          D hdeg h0 a b hm)
    · exact
        recovered_generic_ordinate
          D hdeg h0 E (by omega) hI
  · right
    exact
      N13RankTwoInfinityVerticalGraphRecovery.exists_verticalGraph_of_basis
        (integralInfinityIdeal D hdeg h0) bV hbV

end

end MazurProof.N13ReciprocalInfinityContraction


