-- Prove2me | Definitions.Def_HuangN13_SeparationDataCore
-- name    : HuangN13_SeparationDataCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:57:43.133649+00:00
-- url     : https://prove2.me/theorems/a1e5a159-cf8f-4db7-b532-de1c863dc539
-- title:
--   Exact original statement data for chosen_point_specialClass, specialCode_add, rationalPoint_certified…
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13EffectiveDataCompatibility_exists_certified_realization
import Theorems.Thm_HuangN13_N13SplitQuadraticSpecialRestriction_pairLine_special_restrictions
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub
import Theorems.Thm_MazurProof_N13InfinityBaseChange_infinityCompatible
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_nonZeroDivisors_le_comap

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_xClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (p : K[X]) :
    coordinateMap ι hM (xClass M p) =
      xClass M' (p.map ι) := by
  exact AdjoinRoot.map_of
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM) p
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_yClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    coordinateMap ι hM (yClass M) = yClass M' := by
  exact AdjoinRoot.map_root
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM)
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_ySubClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (v : K[X]) :
    coordinateMap ι hM (ySubClass M v) =
      ySubClass M' (v.map ι) := by
  simp [ySubClass]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- A Mumford graph ideal extends to the coefficient-extended graph ideal. -/
theorem map_mumfordIdeal
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (u v : K[X]) :
    Ideal.map (coordinateMap ι hM) (mumfordIdeal M u v) =
      mumfordIdeal M' (u.map ι) (v.map ι) := by
  rw [mumfordIdeal, mumfordIdeal, Ideal.map_span, Set.image_pair,
    coordinateMap_xClass, coordinateMap_ySubClass]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem invFracMap_mumfordIdealUnit
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
      mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi := by
  apply Units.ext
  simp only [invFracMap, Units.coe_map, coe_mumfordIdealUnit]
  change
    (FractionalIdeal.extendedHom' (FunctionField M')
      (nonZeroDivisors_le_comap ι hι hM))
        (mumfordIdeal M D.u D.v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M'
          (D.u.map ι) (D.v.map ι) :
        FractionalIdeal (CoordinateRing M')⁰ (FunctionField M'))
  calc
    _ =
        (Ideal.map (coordinateMap ι hM)
            (mumfordIdeal M D.u D.v) :
          FractionalIdeal (CoordinateRing M')⁰ (FunctionField M')) :=
      FractionalIdeal.extended_coeIdeal_eq_map
        (FunctionField M')
        (nonZeroDivisors_le_comap ι hι hM)
        (mumfordIdeal M D.u D.v)
    _ = _ := by rw [map_mumfordIdeal]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem orientedFracMap_mumfordRaw
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    orientedFracMap ι hι hM (mumfordRaw M D) =
      mumfordRaw M' (D.mapCoeffs ι hι hM) := by
  apply Prod.ext
  · change
      invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
        mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi
    exact invFracMap_mumfordIdealUnit ι hι hM D
  · rfl
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- The quotient map sends the class of a Mumford graph to the class of its
coefficient extension. -/
@[simp] theorem picMap_classOf
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O')
    (D : Mumford M) :
    picMap ι hι hM O O' hO (classOf M O D) =
      classOf M' O' (D.mapCoeffs ι hι hM) := by
  change
    Additive.ofMul
        ((QuotientGroup.map
          (principalOriented M O).range
          (principalOriented M' O').range
          (orientedFracMap ι hι hM)
          (principalRange_le_comap ι hι hM O O' hO))
            (QuotientGroup.mk' (principalOriented M O).range
              (mumfordRaw M D))) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M' O').range
          (mumfordRaw M' (D.mapCoeffs ι hι hM)))
  rw [QuotientGroup.map_mk', orientedFracMap_mumfordRaw]
  rfl
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
@[simp] theorem picMapRatToQ₂_classOf
    (D : N13Mumford.Mumford ℚ) :
    picMapRatToQ₂
        (SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) D) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (D.mapCoeffs ratToQ₂ ratToQ₂_injective
          (map_n13_f ratToQ₂)) := by
  exact SexticMumford.OrientedBaseChange.picMap_classOf
    ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)
    (N13Infinity.positiveInfinityOrder ℚ)
    (N13Infinity.positiveInfinityOrder Q₂)
    (infinityCompatible ratToQ₂ ratToQ₂_injective) D
end
end MazurProof.N13InfinityBaseChange
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
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
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine generic fibre of the proper integral point line is exactly
the standard sextic point graph. -/
@[simp] theorem map_integralPointTwoChartLine_affineIdeal
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointTwoChartLine P).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralAffinePointSpread.pointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v
  exact N13IntegralAffinePointSpread.map_pointIdeal P
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem lift_t_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.1 : Q₂) = x⁻¹ := by
  rfl
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem lift_v_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.2 : Q₂) = x⁻¹ ^ 3 * y := by
  rfl
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem transportCoeffMap_lift_t
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.1 = x⁻¹ := by
  exact lift_t_coe x y hx hxy
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem transportCoeffMap_lift_v
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.2 = x⁻¹ ^ 3 * y := by
  exact lift_v_coe x y hx hxy
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem x_ne_zero
    (x : Q₂) (hx : x.valuation < 0) :
    x ≠ 0 :=
  N13LocalDlogRegimes.nonintegral_coordinate_ne_zero x hx
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The nonmonic affine closure equation becomes a unit multiple of the
standard monic point equation on the generic fibre. -/
theorem genericU_eq_unit_mul
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    genericU x y hx hxy =
      _root_.Polynomial.C (-((lift x y hx hxy).1.1 : Q₂)) *
        (X - _root_.Polynomial.C x) := by
  simp [genericU, N13IntegralInfinityPointSpread.affineU,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    transportCoeffMap_lift_t, lift_t_coe]
  have hc :
      _root_.Polynomial.C (x⁻¹) * _root_.Polynomial.C x = (1 : Q₂[X]) := by
    rw [← map_mul, inv_mul_cancel₀ (x_ne_zero x hx), map_one]
  linear_combination -hc
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The completed-square graph ordinate evaluates to the standard sextic
ordinate at the generic point. -/
theorem genericV_eval
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (genericV x y hx hxy).eval x = pointY x y := by
  simp [genericV, pointY,
    N13IntegralInfinityPointSpread.affineV,
    N13GoodSexticMumfordTransport.completedGraph,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h, transportCoeffMap_lift_v]
  field_simp [x_ne_zero x hx]
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem standardU_dvd_genericV_sub
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    X - _root_.Polynomial.C x ∣
      genericV x y hx hxy - _root_.Polynomial.C (pointY x y) := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := genericV x y hx hxy) (a := x)
  simpa [genericV_eval x y hx hxy] using h
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
private theorem span_pair_mul_left_unit
    {A : Type*} [CommRing A]
    (a x y : A) (ha : IsUnit a) :
    Ideal.span ({a * x, y} : Set A) =
      Ideal.span ({x, y} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        a (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hax :
          a * x ∈ Ideal.span ({a * x, y} : Set A) :=
        Ideal.subset_span (by simp)
      have hbx := Ideal.mul_mem_left _ b hax
      simpa [← mul_assoc, hba] using hbx
    · rw [hz]
      exact Ideal.subset_span (by simp)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem genericU_scalar_isUnit
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    IsUnit
      (SexticMumford.xClass Model
        (_root_.Polynomial.C (-((lift x y hx hxy).1.1 : Q₂)))) := by
  have ht :
      -((lift x y hx hxy).1.1 : Q₂) ≠ 0 := by
    simp [lift_t_coe, x_ne_zero x hx]
  have hu : IsUnit (-((lift x y hx hxy).1.1 : Q₂)) :=
    isUnit_iff_ne_zero.mpr ht
  change
    IsUnit
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model)
        (-((lift x y hx hxy).1.1 : Q₂)))
  exact
    hu.map
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model))
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem mumfordIdeal_genericU_eq_standardU
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      SexticMumford.mumfordIdeal Model
        (X - _root_.Polynomial.C x) (genericV x y hx hxy) := by
  rw [SexticMumford.mumfordIdeal,
    genericU_eq_unit_mul,
    SexticMumford.xClass_mul]
  exact
    span_pair_mul_left_unit
      (SexticMumford.xClass Model
        (_root_.Polynomial.C (-((lift x y hx hxy).1.1 : Q₂))))
      (SexticMumford.xClass Model (X - _root_.Polynomial.C x))
      (SexticMumford.ySubClass Model
        (genericV x y hx hxy))
      (genericU_scalar_isUnit x y hx hxy)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fibre of the escaping two-chart line is exactly the
standard sextic point graph. -/
theorem genericIdeal_eq_standardPoint
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x y hx hxy)) =
      SexticMumford.mumfordIdeal Model
        (X - _root_.Polynomial.C x) (_root_.Polynomial.C (pointY x y)) := by
  rw [N13IntegralInfinityPointSpread.map_affinePointIdeal]
  change
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      _
  rw [mumfordIdeal_genericU_eq_standardU]
  exact
    N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
      (X - _root_.Polynomial.C x) (genericV x y hx hxy) (_root_.Polynomial.C (pointY x y))
      (standardU_dvd_genericV_sub x y hx hxy)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem genericIdeal_eq_pointMumford
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x y hx hxy)) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (curvePoint x y hxy)).u
        (SexticMumford.pointMumford Model
          (curvePoint x y hxy)).v := by
  simpa [curvePoint, SexticMumford.pointMumford,
    SexticMumford.affinePointMumford] using
      genericIdeal_eq_standardPoint x y hx hxy
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The trivial line in the explicit two-chart presentation. -/
def one : TwoChartLine where
  affineIdeal := ⊤
  infinityIdeal := ⊤
  affine_isUnit := by
    rw [FractionalIdeal.coeIdeal_top]
    exact isUnit_one
  infinity_isUnit := by
    rw [FractionalIdeal.coeIdeal_top]
    exact isUnit_one
  overlap_eq := by
    rw [Ideal.map_top, Ideal.map_top]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tensor_affineIdeal (L M : TwoChartLine) :
    (tensor L M).affineIdeal =
      L.affineIdeal * M.affineIdeal :=
  rfl
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem tensor_infinityIdeal (L M : TwoChartLine) :
    (tensor L M).infinityIdeal =
      L.infinityIdeal * M.infinityIdeal :=
  rfl
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
/-- Natural tensor powers of an explicit two-chart line.  Natural powers
are sufficient for balanced low-degree Mumford representatives because
their infinity multiplicity is nonnegative. -/
def tensorPow
    (L : TwoChartLine) :
    ℕ → TwoChartLine
  | 0 => one
  | n + 1 => tensor L (tensorPow L n)
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tensorPow_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensorPow L n).affineIdeal =
      L.affineIdeal ^ n := by
  induction n with
  | zero =>
      simp [tensorPow, one]
  | succ n ih =>
      simp [tensorPow, ih, pow_succ']
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem tensorPow_infinityIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensorPow L n).infinityIdeal =
      L.infinityIdeal ^ n := by
  induction n with
  | zero =>
      simp [tensorPow, one]
  | succ n ih =>
      simp [tensorPow, ih, pow_succ']
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
/-- The natural tensor power of the positive-infinity point line.  Balanced
low-degree Mumford data use only nonnegative infinity multiplicities. -/
def positiveInfinityPowerLine
    (n : ℕ) :
    TwoChartLine :=
  tensorPow infinityPlusLine n
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem positiveInfinityPowerLine_affineIdeal
    (n : ℕ) :
    (positiveInfinityPowerLine n).affineIdeal = ⊤ := by
  simp [positiveInfinityPowerLine]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Tensoring by a positive-infinity power changes only the infinity chart.
In particular it preserves the exact affine generic ideal of any previously
constructed proper spread. -/
@[simp] theorem tensor_positiveInfinityPowerLine_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensor L (positiveInfinityPowerLine n)).affineIdeal =
      L.affineIdeal := by
  simp
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
/-- Add a nonnegative positive-infinity multiplicity to a proper line.
This supplies the chart-level factor needed for the `nInf` field of a
balanced low-degree Mumford representative; identifying the resulting line
with the oriented Picard class is a separate semantic comparison. -/
def withPositiveInfinityMultiplicity
    (L : TwoChartLine) (n : ℕ) :
    TwoChartLine :=
  tensor L (positiveInfinityPowerLine n)
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem withPositiveInfinityMultiplicity_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (withPositiveInfinityMultiplicity L n).affineIdeal =
      L.affineIdeal :=
  tensor_positiveInfinityPowerLine_affineIdeal L n
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Adding the positive-infinity correction preserves the exact Mumford
ideal seen on the generic affine chart. -/
theorem map_withPositiveInfinityMultiplicity_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (withPositiveInfinityMultiplicity L n).affineIdeal =
      Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        L.affineIdeal := by
  rw [withPositiveInfinityMultiplicity_affineIdeal]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Inverse completed-square ordinate over `ℚ₂`. -/
def goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂ :=
  (Y - N13GoodModelTwo.h x) / 2
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Restriction of a natural tensor power is the corresponding power of the
reduced affine ideal. -/
@[simp] theorem restrict_tensorPow_affineIdeal
    (L : Line) (n : ℕ) :
    (restrict (N13TwoChartLineTensor.tensorPow L n)).affineIdeal =
      (restrict L).affineIdeal ^ n := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13TwoChartLineTensor.tensorPow L n).affineIdeal =
      (Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        L.affineIdeal) ^ n
  rw [N13TwoChartLineTensor.tensorPow_affineIdeal, Ideal.map_pow]
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction of a natural tensor power is the corresponding power of the
reduced infinity ideal. -/
@[simp] theorem restrict_tensorPow_infinityIdeal
    (L : Line) (n : ℕ) :
    (restrict (N13TwoChartLineTensor.tensorPow L n)).infinityIdeal =
      (restrict L).infinityIdeal ^ n := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13TwoChartLineTensor.tensorPow L n).infinityIdeal =
      (Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        L.infinityIdeal) ^ n
  rw [N13TwoChartLineTensor.tensorPow_infinityIdeal, Ideal.map_pow]
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralFunctionFieldFractionRing MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coercing the generic ideal unit to a fractional ideal recovers the
literal extension of the line's affine ideal.

This bridge is independent of the geometric origin of the proper line and is
therefore shared by point and quadratic Picard realizations. -/
@[simp] theorem coe_genericIdealUnit
    (L : Line) :
    (genericIdealUnit L :
        N13IntegralFractionalHull.RationalFractionalIdeal) =
      (Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal :
        N13IntegralFractionalHull.RationalFractionalIdeal) := by
  change
    N13IntegralFractionalHull.extendFractional
        (L.affine_isUnit.unit :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      _
  rw [L.affine_isUnit.unit_spec,
    N13IntegralFractionalHull.extendFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Equality of mapped generic affine ideals determines equality of their
packaged fractional-ideal units.

The statement retains the exact Mumford representative rather than passing
prematurely to the oriented Picard quotient. -/
theorem genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericIdealUnit L =
      SexticMumford.mumfordIdealUnit Model D.toSemi := by
  apply Units.ext
  rw [coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      hmap
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A proper line with the exact Mumford affine ideal realizes the literal
oriented Mumford datum when marked by the representative's exponent
`nInf - 1`.

This is the generic-fibre bridge used uniformly by point and quadratic
two-chart realizations. -/
theorem genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericRaw L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D := by
  apply Prod.ext
  · exact
      genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
        L D hmap
  · rfl
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact mapped-ideal equality also identifies the induced generic Picard
class with the standard oriented class of the Mumford representative. -/
theorem genericClass_eq_classOf_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericClass L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        D := by
  unfold genericClass SexticMumford.classOf
  rw [genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq L D hmap]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
namespace Data
/-- The special Abel class represented by the same proper line after
chartwise reduction. -/
def toSpecialPic (D : Data) : SpecialPic :=
  N13AbelFiberTwoModel.abel D.specialDivisor
end Data
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The explicit sheet-zero point is the fixed special Abel anchor. -/
theorem specialInfinityPlusPoint_eq_specialAnchor :
    specialInfinityPlusPoint =
      N13RationalPointEndgame.specialAnchor := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  change
    (Sum.inr (), (0 : N13GoodModelTwo.F2)) =
      N13AbelFiberTwoModel.curvePointEquiv
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityPlus)
  rw [N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  rfl
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The explicit sheet-one point is the named negative-infinity cusp on the
special curve. -/
theorem specialInfinityMinusPoint_eq_specialCusp :
    specialInfinityMinusPoint =
      N13SpecialCuspReduction.specialCuspEquiv
        N13Mumford.Cusp13.infinityMinus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  change
    (Sum.inr (), (1 : N13GoodModelTwo.F2)) =
      N13AbelFiberTwoModel.curvePointEquiv
        (N13SpecialCuspReduction.specialCuspEquiv
          N13Mumford.Cusp13.infinityMinus)
  rw [N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  rfl
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
/-- Every natural positive-infinity tensor power restricts on the affine
chart to the corresponding power of the special anchor's unit ideal. -/
theorem restrict_positiveInfinityPowerLine_affineIdeal
    (n : ℕ) :
    (N13TwoChartSpecialRestriction.restrict
      (N13TwoChartLineTensor.positiveInfinityPowerLine n)).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).affineIdeal ^ n := by
  rw [N13TwoChartLineTensor.positiveInfinityPowerLine,
    N13TwoChartSpecialRestriction.restrict_tensorPow_affineIdeal,
    restrict_infinityPlusLine_affineIdeal]
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
/-- Every natural positive-infinity tensor power restricts on the infinity
chart to the corresponding power of the special anchor point ideal. -/
theorem restrict_positiveInfinityPowerLine_infinityIdeal
    (n : ℕ) :
    (N13TwoChartSpecialRestriction.restrict
      (N13TwoChartLineTensor.positiveInfinityPowerLine n)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).infinityIdeal ^ n := by
  rw [N13TwoChartLineTensor.positiveInfinityPowerLine,
    N13TwoChartSpecialRestriction.restrict_tensorPow_infinityIdeal,
    restrict_infinityPlusLine_infinityIdeal]
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Degree-two normalization of an escaping point line by adjoining the
positive-infinity anchor once. -/
def anchoredPointLine
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  N13TwoChartLineTensor.withPositiveInfinityMultiplicity
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x y hx hxy)
    1
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The intended special divisor of the anchored escaping point line. -/
def anchoredDivisor
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(N13ProperCurveReduction.reduceNonintegralAffine x y hx hxy,
    N13RationalPointEndgame.specialAnchor)
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The affine restriction of the anchored point line equals the affine
chart ideal of its literal anchored special divisor. -/
theorem restrict_anchoredPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine x y hx hxy)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (anchoredDivisor x y hx hxy)).affineIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    anchoredDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityPointSpread.nonintegralPointLine
          x y hx hxy)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy)).affineIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).affineIdeal
  rw [restrict_nonintegralPointLine_affineIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_affineIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The infinity restriction of the anchored point line equals the infinity
chart ideal of the same literal anchored special divisor. -/
theorem restrict_anchoredPointLine_infinityIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine x y hx hxy)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (anchoredDivisor x y hx hxy)).infinityIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    anchoredDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityPointSpread.nonintegralPointLine
          x y hx hxy)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (N13ProperCurveReduction.reduceNonintegralAffine
            x y hx hxy)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).infinityIdeal
  rw [restrict_nonintegralPointLine_infinityIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_infinityIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The finite base and sheet coordinates of the reduced point are the
coefficientwise residues of the integral coordinates. -/
@[simp] theorem curvePointEquiv_reducedPoint
    (P : IntegralPoint) :
    N13AbelFiberTwoModel.curvePointEquiv (reducedPoint P) =
      (Sum.inl (PadicInt.toZMod P.1.1),
        PadicInt.toZMod P.1.2) :=
  rfl
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
/-- Place the reduced point in the degree-two Abel model by adjoining the
chosen positive-infinity anchor exactly once. -/
def anchoredReducedDivisor
    (P : IntegralPoint) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(reducedPoint P, N13RationalPointEndgame.specialAnchor)
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- Degree-two normalization of an integral affine point line by adjoining
the positive-infinity anchor once. -/
def anchoredPointLine
    (P : IntegralPoint) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  N13TwoChartLineTensor.withPositiveInfinityMultiplicity
    (N13FiniteAffineTwoChart.integralPointTwoChartLine P)
    1
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- The affine restriction of the anchored integral point line is exactly
the affine chart ideal of its literal anchored special divisor. -/
theorem restrict_anchoredPointLine_affineIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine P)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P)).affineIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (N13IntegralAffinePointSpecialClass.reducedPoint P)).affineIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).affineIdeal
  rw [restrict_integralPointTwoChartLine_affineIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_affineIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- The infinity restriction of the anchored integral point line is exactly
the infinity chart ideal of the same literal anchored special divisor. -/
theorem restrict_anchoredPointLine_infinityIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (anchoredPointLine P)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P)).infinityIdeal := by
  rw [anchoredPointLine,
    N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13TwoChartLineTensor.positiveInfinityPowerLine 1)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          N13RationalPointEndgame.specialAnchor).infinityIdeal
  rw [restrict_integralPointTwoChartLine_infinityIdeal,
    N13InfinityLineSpecialRestriction.restrict_positiveInfinityPowerLine_infinityIdeal,
    pow_one,
    ← N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The good completed-square sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The degree-one Mumford representative of an integral affine point. -/
abbrev degreeOneMumford
    (P : IntegralPoint) :
    SexticMumford.Mumford Model :=
  SexticMumford.pointMumford Model
    (N13IntegralAffinePointSpread.curvePoint P)
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
/-- Full two-fibre realization data for an integral affine point.

The positive-infinity tensor factor supplies special degree two, while the
oriented generic exponent `-1` records the affine point's zero infinity
multiplicity relative to the positive base point. -/
def data
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.Data where
  charts :=
    N13FiniteAffinePointInfinityClosure.anchoredPointLine P
  infinityOrder := -1
  specialDivisor :=
    N13IntegralAffinePointSpecialClass.anchoredReducedDivisor P
  special_affine :=
    N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_affineIdeal
      P
  special_infinity :=
    N13FiniteAffinePointInfinityClosure.restrict_anchoredPointLine_infinityIdeal
      P
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The positive-infinity anchor is trivial on the generic affine chart, so
the anchored line still has the standard Mumford ideal of the original
integral point. -/
theorem map_anchoredPointLine_affineIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (degreeOneMumford P).u
        (degreeOneMumford P).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P).affineIdeal =
      _
  rw [N13FiniteAffinePointInfinityClosure.anchoredPointLine,
    N13TwoChartLineTensor.map_withPositiveInfinityMultiplicity_affineIdeal]
  exact
    N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal P
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fractional-ideal unit of the anchored integral line is
exactly the unit packaged by its degree-one Mumford representative. -/
theorem genericIdealUnit_anchoredPointLine_eq_pointMumford
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericIdealUnit
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) =
      SexticMumford.mumfordIdealUnit Model
        (degreeOneMumford P).toSemi := by
  apply Units.ext
  rw [N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      (map_anchoredPointLine_affineIdeal P)
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The raw oriented datum of the anchored integral line is literally the
Mumford raw datum: their ideal units agree and both exponents are `-1`. -/
theorem genericRaw_anchoredPointLine_eq_mumfordRaw
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericRaw
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford P) := by
  apply Prod.ext
  · change
      N13TwoChartPicardRealization.genericIdealUnit
          (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) =
        SexticMumford.mumfordIdealUnit Model
          (degreeOneMumford P).toSemi
    exact
      genericIdealUnit_anchoredPointLine_eq_pointMumford P
  · change
      Multiplicative.ofAdd (-1 : ℤ) =
        Multiplicative.ofAdd
          (((degreeOneMumford P).nInf : ℤ) - 1)
    simp [degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The generic class carried by the integral point's two-fibre data is the
standard oriented Picard class of its Mumford representative. -/
theorem data_toGenericPic_eq_classOf
    (P : IntegralPoint) :
    (data P).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (degreeOneMumford P) := by
  change
    N13TwoChartPicardRealization.genericClass
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (degreeOneMumford P)
  unfold N13TwoChartPicardRealization.genericClass
    SexticMumford.classOf
  rw [genericRaw_anchoredPointLine_eq_mumfordRaw]
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The good completed-square sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13TwoChartPicardRealization.Model
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The balanced degree-one Mumford representative of the original affine
point.  Its infinity multiplicity is zero because the point is affine. -/
abbrev degreeOneMumford
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.Mumford Model :=
  SexticMumford.pointMumford Model
    (N13EscapingDegreeOneSpread.curvePoint x y hxy)
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Full two-fibre realization data for an escaping degree-one Mumford point.

The positive-infinity tensor factor supplies special degree two.  The marked
generic order remains `-1`, which is the oriented exponent of an affine
degree-one Mumford representative. -/
def data
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.Data where
  charts :=
    N13EscapingPointSpecialRestriction.anchoredPointLine
      x y hx hxy
  infinityOrder := -1
  specialDivisor :=
    N13EscapingPointSpecialRestriction.anchoredDivisor
      x y hx hxy
  special_affine :=
    N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_affineIdeal
      x y hx hxy
  special_infinity :=
    N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_infinityIdeal
      x y hx hxy
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Adding the positive-infinity anchor leaves the generic affine ideal
unchanged, so it remains the standard Mumford ideal of the original point. -/
theorem map_anchoredPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (degreeOneMumford x y hxy).u
        (degreeOneMumford x y hxy).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy).affineIdeal =
      _
  rw [N13EscapingPointSpecialRestriction.anchoredPointLine,
    N13TwoChartLineTensor.map_withPositiveInfinityMultiplicity_affineIdeal]
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (N13EscapingDegreeOneSpread.lift x y hx hxy)) =
      _
  exact
    N13EscapingDegreeOneSpread.genericIdeal_eq_pointMumford
      x y hx hxy
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fractional-ideal unit of the anchored proper line is exactly
the unit packaged by the degree-one Mumford representative. -/
theorem genericIdealUnit_anchoredPointLine_eq_pointMumford
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericIdealUnit
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy) =
      SexticMumford.mumfordIdealUnit Model
        (degreeOneMumford x y hxy).toSemi := by
  apply Units.ext
  rw [N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      (map_anchoredPointLine_affineIdeal x y hx hxy)
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The oriented raw datum of the anchored line is literally the Mumford raw
datum; the ideal units agree and both oriented exponents are `-1`. -/
theorem genericRaw_anchoredPointLine_eq_mumfordRaw
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericRaw
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford x y hxy) := by
  apply Prod.ext
  · change
      N13TwoChartPicardRealization.genericIdealUnit
          (N13EscapingPointSpecialRestriction.anchoredPointLine
            x y hx hxy) =
        SexticMumford.mumfordIdealUnit Model
          (degreeOneMumford x y hxy).toSemi
    exact
      genericIdealUnit_anchoredPointLine_eq_pointMumford
        x y hx hxy
  · change
      Multiplicative.ofAdd (-1 : ℤ) =
        Multiplicative.ofAdd
          (((degreeOneMumford x y hxy).nInf : ℤ) - 1)
    simp [degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Consequently the generic Picard class carried by the two-fibre data is
the standard oriented class of the original degree-one Mumford point. -/
theorem data_toGenericPic_eq_classOf
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (data x y hx hxy).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        (degreeOneMumford x y hxy) := by
  change
    N13TwoChartPicardRealization.genericClass
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        (degreeOneMumford x y hxy)
  unfold N13TwoChartPicardRealization.genericClass
    SexticMumford.classOf
  rw [genericRaw_anchoredPointLine_eq_mumfordRaw]
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
/-- Proper two-chart lines on the integral good model. -/
abbrev Line : Type :=
  N13TwoChartPicardRealization.Line
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Package one proper line and its two exact special chart comparisons as
two-fibre Picard data for a chosen Mumford representative.

The generic affine ideal equality is not needed to construct the data; it is
consumed separately to identify the resulting generic class. -/
def dataOfSpecialRealization
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal) :
    N13TwoChartPicardRealization.Data where
  charts := L
  infinityOrder := (D.nInf : ℤ) - 1
  specialDivisor := Δ
  special_affine := haffine
  special_infinity := hinfinity
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic Picard class of the packaged realization is the standard
oriented class of the same Mumford representative. -/
theorem dataOfSpecialRealization_toGenericPic_eq_classOf
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    (dataOfSpecialRealization
      D L Δ haffine hinfinity).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D := by
  change
    N13TwoChartPicardRealization.genericClass
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D
  exact
    N13TwoChartPicardRealization.genericClass_eq_classOf_of_map_affineIdeal_eq
      L D hmap
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The doubled positive-infinity line used for the identity class. -/
def infinityPlusLine : N13TwoChartPicardRealization.Line :=
  N13TwoChartLineTensor.tensor
    N13TwoChartLineTensor.infinityPlusLine
    N13TwoChartLineTensor.infinityPlusLine
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The special divisor consisting of two copies of the positive anchor. -/
def infinityPlusDivisor :
    N13TwoChartPicardRealization.EffectiveDivisorTwo :=
  s(N13InfinityLineSpecialRestriction.specialInfinityPlusPoint,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint)
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The positive-infinity construction restricts to the exact chart pair of
the doubled special anchor. -/
theorem restrict_infinityPlusLine_eq_ofDivisor :
    N13TwoChartSpecialRestriction.restrict infinityPlusLine =
      N13SpecialDivisorCharts.ofDivisor infinityPlusDivisor := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · simp only [infinityPlusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
      infinityPlusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal]
  · simp only [infinityPlusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
      infinityPlusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal]
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The doubled positive-infinity line has the unit generic affine ideal,
which is the Mumford ideal of the balanced identity representative. -/
theorem map_infinityPlusLine_affineIdeal :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        infinityPlusLine.affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.zero Model).u
        (SexticMumford.zero Model).v := by
  rw [infinityPlusLine,
    N13TwoChartLineTensor.tensor_affineIdeal,
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.top_mul, Ideal.map_top]
  exact (SexticMumford.zero_mumfordIdeal Model).symm
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Complete two-fibre data for the positive infinity base point. -/
def infinityPlusData :
    N13TwoChartPicardRealization.Data :=
  N13SplitQuadraticPicardRealization.dataOfSpecialRealization
    (SexticMumford.zero Model)
    infinityPlusLine
    infinityPlusDivisor
    (congrArg
      (fun C => C.affineIdeal)
      restrict_infinityPlusLine_eq_ofDivisor)
    (congrArg
      (fun C => C.infinityIdeal)
      restrict_infinityPlusLine_eq_ofDivisor)
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The generic class of the positive-infinity data is the identity
Abel--Jacobi class. -/
theorem infinityPlusData_toGenericPic :
    infinityPlusData.toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (SexticMumford.zero Model) := by
  exact
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
      (SexticMumford.zero Model)
      infinityPlusLine
      infinityPlusDivisor
      (congrArg
        (fun C => C.affineIdeal)
        restrict_infinityPlusLine_eq_ofDivisor)
      (congrArg
        (fun C => C.infinityIdeal)
        restrict_infinityPlusLine_eq_ofDivisor)
      map_infinityPlusLine_affineIdeal
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The special class of the positive-infinity data is the doubled special
anchor used by the rational-point endgame. -/
theorem infinityPlusData_toSpecialPic :
    infinityPlusData.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        N13InfinityLineSpecialRestriction.specialInfinityPlusPoint := by
  rfl
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The anchored negative-infinity line remembers the two distinct infinity
sheets while presenting an effective divisor of degree two. -/
def infinityMinusLine : N13TwoChartPicardRealization.Line :=
  N13TwoChartLineTensor.tensor
    N13TwoChartLineTensor.infinityMinusLine
    N13TwoChartLineTensor.infinityPlusLine
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The special divisor formed by the negative infinity point and the fixed
positive anchor. -/
def infinityMinusDivisor :
    N13TwoChartPicardRealization.EffectiveDivisorTwo :=
  s(N13InfinityLineSpecialRestriction.specialInfinityMinusPoint,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint)
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The anchored negative-infinity construction restricts to the literal
chart pair retaining both special sheets. -/
theorem restrict_infinityMinusLine_eq_ofDivisor :
    N13TwoChartSpecialRestriction.restrict infinityMinusLine =
      N13SpecialDivisorCharts.ofDivisor infinityMinusDivisor := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · simp only [infinityMinusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
      infinityMinusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_affineIdeal,
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal]
  · simp only [infinityMinusLine,
      N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
      infinityMinusDivisor, N13SpecialDivisorCharts.ofDivisor_mk,
      N13SpecialDivisorCharts.tensor]
    rw [
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_infinityIdeal,
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal]
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The anchored negative-infinity line has the unit generic affine ideal,
matching the standard negative-infinity Mumford representative. -/
theorem map_infinityMinusLine_affineIdeal :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        infinityMinusLine.affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.infinityMinusMumford Model).u
        (SexticMumford.infinityMinusMumford Model).v := by
  rw [infinityMinusLine,
    N13TwoChartLineTensor.tensor_affineIdeal,
    N13TwoChartLineTensor.infinityMinusLine_affineIdeal,
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.top_mul, Ideal.map_top]
  exact (SexticMumford.zero_mumfordIdeal Model).symm
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Complete two-fibre data for the negative infinity point. -/
def infinityMinusData :
    N13TwoChartPicardRealization.Data :=
  N13SplitQuadraticPicardRealization.dataOfSpecialRealization
    (SexticMumford.infinityMinusMumford Model)
    infinityMinusLine
    infinityMinusDivisor
    (congrArg
      (fun C => C.affineIdeal)
      restrict_infinityMinusLine_eq_ofDivisor)
    (congrArg
      (fun C => C.infinityIdeal)
      restrict_infinityMinusLine_eq_ofDivisor)
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The generic class of the negative-infinity data is the standard
difference of the two infinity points. -/
theorem infinityMinusData_toGenericPic :
    infinityMinusData.toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        (SexticMumford.infinityMinusMumford Model) := by
  exact
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
      (SexticMumford.infinityMinusMumford Model)
      infinityMinusLine
      infinityMinusDivisor
      (congrArg
        (fun C => C.affineIdeal)
        restrict_infinityMinusLine_eq_ofDivisor)
      (congrArg
        (fun C => C.infinityIdeal)
        restrict_infinityMinusLine_eq_ofDivisor)
      map_infinityMinusLine_affineIdeal
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
/-- The special class of the negative-infinity data is its anchored proper
reduction. -/
theorem infinityMinusData_toSpecialPic :
    infinityMinusData.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        N13InfinityLineSpecialRestriction.specialInfinityMinusPoint := by
  rfl
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem goodY_zero_one : N13TwoChartLineTensor.goodY (0 : Q₂) 1 = 0 := by
  simp [N13TwoChartLineTensor.goodY, N13GoodModelTwo.h]
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem goodY_negOne_one : N13TwoChartLineTensor.goodY (-1 : Q₂) 1 = 1 := by
  simp [N13TwoChartLineTensor.goodY, N13GoodModelTwo.h]; norm_num
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem curve_zero : N13GoodModelTwo.AffineEquation (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1) := by
  rw [goodY_zero_one]; simp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs]
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem curve_negOne : N13GoodModelTwo.AffineEquation (-1 : Q₂) (N13TwoChartLineTensor.goodY (-1) 1) := by
  rw [goodY_negOne_one]; norm_num [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs]
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13InverseInfinityData.instFactPrimeOfNatNat_fLT
theorem reducedPoint_zero :
    reducedPoint (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1) curve_zero =
      N13SpecialCuspReduction.specialCuspEquiv .zeroPlus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  have hx : ‖(0 : Q₂)‖ ≤ 1 := by simp
  rw [reducedPoint, dif_pos hx, N13IntegralAffinePointSpecialClass.curvePointEquiv_reducedPoint,
    N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  simp only [N13SpecialCuspReduction.cuspCoordinate, N13ProperCurveReduction.integralAffineLift]
  ext
  · simp
  · show PadicInt.toZMod _ = 0
    rw [toZMod_mk_of_eq _ 0 _ (by simp) goodY_zero_one]
    exact map_zero _
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13InverseInfinityData.instFactPrimeOfNatNat_fLT
theorem reducedPoint_negOne :
    reducedPoint (-1 : Q₂) (N13TwoChartLineTensor.goodY (-1) 1) curve_negOne =
      N13SpecialCuspReduction.specialCuspEquiv .negOnePlus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  have hx : ‖(-1 : Q₂)‖ ≤ 1 := by simp
  rw [reducedPoint, dif_pos hx, N13IntegralAffinePointSpecialClass.curvePointEquiv_reducedPoint,
    N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  simp only [N13SpecialCuspReduction.cuspCoordinate, N13ProperCurveReduction.integralAffineLift]
  ext
  · simp
  · show PadicInt.toZMod _ = 1
    rw [toZMod_mk_of_eq _ 1 _ (by simp) goodY_negOne_one]
    exact map_one _
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InverseInfinityData
noncomputable section
open N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem reducedPairDivisor_inverseInfinity :
    reducedPairDivisor (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1)
        (-1) (N13TwoChartLineTensor.goodY (-1) 1) curve_zero curve_negOne =
      s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
        N13SpecialCuspReduction.specialCuspEquiv .negOnePlus) := by
  rw [reducedPairDivisor, reducedPoint_zero, reducedPoint_negOne]
end
end MazurProof.N13InverseInfinityData
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace MazurProof.N13Arithmetic
/-- The point encoding specified in the N13 arithmetic interface. -/
abbrev Point13 := AffinePoint13 ⊕ Bool
end MazurProof.N13Arithmetic
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace MazurProof.N13Arithmetic
/-- The second infinity tag. -/
def T : Point13 := Sum.inr true
end MazurProof.N13Arithmetic
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- Identify the proposed point type with the repository's existing
projective sextic point type, preserving both infinity branches. -/
def point13EquivCurvePoint :
    Point13 ≃ SexticMumford.CurvePoint (N13Mumford.model ℚ) where
  toFun := fun
    | Sum.inl ⟨⟨x, y⟩, h⟩ => N13Mumford.affineCurvePoint x y h
    | Sum.inr false => .infinityPlus
    | Sum.inr true => .infinityMinus
  invFun := fun
    | .infinityPlus => Sum.inr false
    | .infinityMinus => Sum.inr true
    | .affine x y h => Sum.inl ⟨(x, y), by
        change y ^ 2 = N13CurveModel.sexticF13 x
        change y ^ 2 = (N13Mumford.f ℚ).eval x at h
        exact h.trans (N13Mumford.f_eval_eq_sexticF13 x)⟩
  left_inv P := by
    cases P with
    | inl P =>
        rcases P with ⟨⟨x, y⟩, h⟩
        rfl
    | inr b =>
        cases b <;> rfl
  right_inv P := by
    cases P <;> rfl
end MazurProof.N13Arithmetic
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- Abel--Jacobi with O = infinityPlus as base point, expressed on Point13. -/
def AJ13 (P : Point13) : J13 :=
  N13MumfordAbelJacobi.abelJacobi ℚ (point13EquivCurvePoint P)
end MazurProof.N13Arithmetic
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N13InverseInfinityWitness
open N13SplitQuadraticSpecialRestriction MazurProof.N13InverseInfinityData
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The proper cusp-pair line through `(0, 0)` and `(-1, 1)` in good coordinates. -/
abbrev caLine : N13TwoChartPicardRealization.Line :=
  N13QuadraticTwoChartSpread.pairLine
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1) curve_zero curve_negOne
end MazurProof.N13InverseInfinityWitness
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N13InverseInfinityWitness
open N13SplitQuadraticSpecialRestriction MazurProof.N13InverseInfinityData
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The candidate nInf = 2 two-fibre datum. -/
def inverseInfinityData : N13TwoChartPicardRealization.Data where
  charts := caLine
  infinityOrder := -2
  specialDivisor :=
    s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
      N13SpecialCuspReduction.specialCuspEquiv .negOnePlus)
  special_affine := by
    rw [(fun x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ => (HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).1), reducedPairDivisor_inverseInfinity]
  special_infinity := by
    rw [(fun x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ => (HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).2), reducedPairDivisor_inverseInfinity]
end MazurProof.N13InverseInfinityWitness
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
def chooseUncalibrated (P : G) : Data := Classical.choose (HuangN13.N13EffectiveDataCompatibility.exists_certified_realization P)
end
end MazurProof.N13EffectiveDataCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Complete chartwise data realizing one rational point on both fibres. -/
structure Data (P : RationalCurvePoint) where
  realization : N13TwoChartPicardRealization.Data
  generic_eq :
    realization.toGenericPic =
      N13InfinityBaseChange.picMapRatToQ₂
        (N13RationalPointEndgame.rationalAbel P)
  special_eq :
    realization.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        (N13ProperCurveReduction.reduceCurve P)
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Balanced Mumford representatives are equal when their three data fields
agree; all remaining structure fields are propositions. -/
private theorem mumford_eq_of_u_v_nInf
    {D E : SexticMumford.Mumford N13TwoChartPicardRealization.Model}
    (hu : D.u = E.u)
    (hv : D.v = E.v)
    (hn : D.nInf = E.nInf) :
    D = E := by
  cases D
  cases E
  simp_all
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Two-fibre realization of the positive infinity base point. -/
def infinityPlusData : Data .infinityPlus where
  realization :=
    N13InfinityPointPicardRealization.infinityPlusData
  generic_eq := by
    rw [N13InfinityPointPicardRealization.infinityPlusData_toGenericPic]
    simp [N13RationalPointEndgame.rationalAbel,
      N13MumfordAbelJacobi.abelJacobi, SexticMumford.pointMumford]
  special_eq := by
    rw [N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic]
    change
      N13RationalPointEndgame.specialPointClass
          N13InfinityLineSpecialRestriction.specialInfinityPlusPoint =
        N13RationalPointEndgame.specialPointClass
          N13RationalPointEndgame.specialAnchor
    exact congrArg N13RationalPointEndgame.specialPointClass
      N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Two-fibre realization of the negative infinity point. -/
def infinityMinusData : Data .infinityMinus where
  realization :=
    N13InfinityPointPicardRealization.infinityMinusData
  generic_eq := by
    rw [N13InfinityPointPicardRealization.infinityMinusData_toGenericPic]
    rw [show N13RationalPointEndgame.rationalAbel
          (.infinityMinus : RationalCurvePoint) =
        SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.infinityMinusMumford
            (N13Mumford.model ℚ)) by rfl,
      N13InfinityBaseChange.picMapRatToQ₂_classOf]
    congr 1
    apply mumford_eq_of_u_v_nInf <;>
      simp [SexticMumford.infinityMinusMumford]
  special_eq := by
    rw [N13InfinityPointPicardRealization.infinityMinusData_toSpecialPic]
    change
      N13RationalPointEndgame.specialPointClass
          N13InfinityLineSpecialRestriction.specialInfinityMinusPoint =
        N13RationalPointEndgame.specialPointClass
          (N13SpecialCuspReduction.specialCuspEquiv
            N13Mumford.Cusp13.infinityMinus)
    exact congrArg N13RationalPointEndgame.specialPointClass
      N13InfinityLineSpecialRestriction.specialInfinityMinusPoint_eq_specialCusp
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Two-fibre realization of an affine rational point whose two-adic first
coordinate is integral. -/
def integralAffineData
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1) :
    Data (.affine X Y hcurve) := by
  -- Rewrite the input equation in the sextic form expected by the good-model
  -- coordinate change; this changes presentation, not the rational point.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  -- The good model keeps `x` and replaces `Y` by the completed-square
  -- ordinate.  These are the coordinates whose integrality controls the
  -- proper reduction chart.
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  -- In the integral branch the two-adic point lifts to an integral point of
  -- the affine spread, whose anchored line supplies both chart ideals.
  let P₂ : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  let R : N13TwoChartPicardRealization.Data :=
    N13IntegralPointPicardRealization.data P₂
  let sourceD : N13Mumford.Mumford ℚ :=
    SexticMumford.pointMumford
      (N13Mumford.model ℚ) (.affine X Y hcurve)
  let targetD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    N13IntegralPointPicardRealization.degreeOneMumford P₂
  let mappedD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    sourceD.mapCoeffs
      N13InfinityBaseChange.ratToQ₂
      N13InfinityBaseChange.ratToQ₂_injective
      (N13InfinityBaseChange.map_n13_f
        N13InfinityBaseChange.ratToQ₂)
  -- Undoing the good-model ordinate change recovers the original sextic
  -- ordinate after base change.  This identity is the only non-definitional
  -- part of comparing the two point representatives.
  have hsexticY :
      N13IntegralAffinePointSpread.sexticY P₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [P₂, N13ProperCurveReduction.integralAffineLift,
      x₂, y₂, N13IntegralAffinePointSpread.sexticY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- Equality of the affine graph polynomial `u`, ordinate polynomial `v`,
  -- and infinity orientation identifies the entire balanced representative.
  have hu :
      targetD.u = mappedD.u := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      P₂, N13ProperCurveReduction.integralAffineLift, x₂]
  have hv :
      targetD.v = mappedD.v := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      hsexticY, N13ProperCurveReduction.ratToQ₂]
  have hn :
      targetD.nInf = mappedD.nInf := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
  have htarget :
      targetD = mappedD :=
    mumford_eq_of_u_v_nInf hu hv hn
  refine
    { realization := R
      generic_eq := ?_
      special_eq := ?_ }
  · rw [show R.toGenericPic =
        SexticMumford.classOf
          N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder
            N13ProperCurveReduction.Q₂)
          targetD by
        exact N13IntegralPointPicardRealization.data_toGenericPic_eq_classOf P₂]
    rw [htarget]
    exact
      (N13InfinityBaseChange.picMapRatToQ₂_classOf sourceD).symm
  · change
      N13RationalPointEndgame.specialPointClass
          (N13IntegralAffinePointSpecialClass.reducedPoint P₂) =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve (.affine X Y hcurve))
    -- The total reduction function branches on the same norm condition as
    -- this construction, so its special point is literally the integral
    -- affine reduction already carried by `R`.
    have hreduce :
        N13ProperCurveReduction.reduceCurve (.affine X Y hcurve) =
          N13ProperCurveReduction.reduceIntegralAffine
            x₂ y₂ hx hgood := by
      simp only [N13ProperCurveReduction.reduceCurve]
      unfold N13ProperCurveReduction.reduceAffine
      dsimp only
      split
      · rfl
      · rename_i hnot
        exact (hnot hx).elim
    rw [hreduce]
    congr 1
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Two-fibre realization of an affine rational point whose first coordinate
escapes the two-adic affine chart. -/
def escapingAffineData
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hxval :
      (N13ProperCurveReduction.ratToQ₂ X).valuation < 0) :
    Data (.affine X Y hcurve) := by
  -- As in the integral branch, first express the rational curve equation in
  -- the sextic presentation used by the good two-adic model.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  -- The completed-square coordinates lie on the good model even though `x₂`
  -- is outside its affine integral chart.
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  let R : N13TwoChartPicardRealization.Data :=
    N13EscapingPointPicardRealization.data x₂ y₂ hxval hgood
  let sourceD : N13Mumford.Mumford ℚ :=
    SexticMumford.pointMumford
      (N13Mumford.model ℚ) (.affine X Y hcurve)
  let targetD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    N13EscapingPointPicardRealization.degreeOneMumford
      x₂ y₂ hgood
  let mappedD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    sourceD.mapCoeffs
      N13InfinityBaseChange.ratToQ₂
      N13InfinityBaseChange.ratToQ₂_injective
      (N13InfinityBaseChange.map_n13_f
        N13InfinityBaseChange.ratToQ₂)
  -- The escaping-chart ordinate is defined by reversing the same coordinate
  -- change, hence it agrees with the original rational `Y` over `ℚ₂`.
  have hpointY :
      N13EscapingDegreeOneSpread.pointY x₂ y₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [x₂, y₂, N13EscapingDegreeOneSpread.pointY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- The escaping line still represents the ordinary degree-one point ideal
  -- on the generic affine chart; only its integral extension uses infinity.
  have hu : targetD.u = mappedD.u := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford, x₂]
  have hv : targetD.v = mappedD.v := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      hpointY, N13ProperCurveReduction.ratToQ₂]
  have hn : targetD.nInf = mappedD.nInf := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
  have htarget : targetD = mappedD :=
    mumford_eq_of_u_v_nInf hu hv hn
  -- Negative valuation is exactly the negation of membership in the
  -- integral norm ball, so the global reduction function must take its
  -- nonintegral branch.
  have hnot : ¬ ‖x₂‖ ≤ 1 := by
    intro hnorm
    have hnonneg : 0 ≤ x₂.valuation :=
      (Padic.norm_le_one_iff_val_nonneg x₂).mp hnorm
    exact (not_lt_of_ge hnonneg) hxval
  refine
    { realization := R
      generic_eq := ?_
      special_eq := ?_ }
  · rw [show R.toGenericPic =
        SexticMumford.classOf
          N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder
            N13ProperCurveReduction.Q₂)
          targetD by
        exact
          N13EscapingPointPicardRealization.data_toGenericPic_eq_classOf
            x₂ y₂ hxval hgood]
    rw [htarget]
    exact
      (N13InfinityBaseChange.picMapRatToQ₂_classOf sourceD).symm
  · change
      N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceNonintegralAffine
            x₂ y₂ hxval hgood) =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve (.affine X Y hcurve))
    have hreduce :
        N13ProperCurveReduction.reduceCurve (.affine X Y hcurve) =
          N13ProperCurveReduction.reduceNonintegralAffine
            x₂ y₂ hxval hgood := by
      simp only [N13ProperCurveReduction.reduceCurve]
      unfold N13ProperCurveReduction.reduceAffine
      dsimp only
      split
      · rename_i hintegral
        exact (hnot hintegral).elim
      · rfl
    rw [hreduce]
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalCurvePointPicardRealization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Every rational point on the projective N13 curve has a proper line whose
generic and special classes are exactly its Abel classes on the two fibres. -/
def data (P : RationalCurvePoint) : Data P := by
  cases P with
  | infinityPlus =>
      exact infinityPlusData
  | infinityMinus =>
      exact infinityMinusData
  | affine X Y hcurve =>
      -- The two-adic norm dichotomy is exhaustive and matches the two
      -- integral models proved above.
      by_cases hx :
          ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1
      · exact integralAffineData X Y hcurve hx
      · have hxval :
            (N13ProperCurveReduction.ratToQ₂ X).valuation < 0 :=
          lt_of_not_ge
            ((Padic.norm_le_one_iff_val_nonneg
              (N13ProperCurveReduction.ratToQ₂ X)).not.mp hx)
        exact escapingAffineData X Y hcurve hxval
end
end MazurProof.N13RationalCurvePointPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
abbrev tClass : G := N13Arithmetic.AJ13 N13Arithmetic.T
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
def choose (P : G) : Data := by
  classical
  exact
    if P = 0 then N13InfinityPointPicardRealization.infinityPlusData
    else if P = tClass then N13InfinityPointPicardRealization.infinityMinusData
    else if P = -tClass then N13InverseInfinityWitness.inverseInfinityData
    else chooseUncalibrated P
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- The two sheets over a base point receive opposite codes. -/
def pointCode (P : N13AbelFiberTwoModel.CurvePoint) : Code :=
  let (B, z) := N13AbelFiberTwoModel.curvePointEquiv P
  if z = 0 then baseAmplitude B else -(baseAmplitude B)
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- Code an unordered degree-two divisor by adding its two point codes. -/
def divisorCode : EffectiveDivisorTwo → Code :=
  Sym2.lift
    ⟨fun P Q => pointCode P + pointCode Q,
     fun P Q => by simp [add_comm]⟩
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
def chosenDivisor (P : G) : EffectiveDivisorTwo := (N13CalibratedChooser.choose P).specialDivisor
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
def specialCode (P : G) : ZMod 19 := divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0)
end
end MazurProof.N13ConstructedSpecialization
end
end


