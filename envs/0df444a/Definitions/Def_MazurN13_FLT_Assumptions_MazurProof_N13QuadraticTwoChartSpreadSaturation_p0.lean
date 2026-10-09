-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpreadSaturation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpreadSaturation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:00:52.145527+00:00
-- url     : https://prove2.me/theorems/391ad4ed-e57e-465c-be16-41653069f959
-- title:
--   FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralPointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingPointPicardRealization_p0

set_option autoImplicit false




/-!
# Vertical saturation of split quadratic N13 spreads

The affine ideal of a two-chart line is invertible in the common function
field.  If two such ideals have no vertical scalar torsion, their product has
none either: multiply by the inverse of the first fractional ideal, cancel the
base scalar in the second ideal, and multiply the first ideal back.

Applying this cancellation theorem to the valuation-independent point-line
constructor proves vertical saturation of `pairLine`.  Coincident points are
allowed, so the result covers both split secants and repeated-root tangents.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13QuadraticTwoChartSpreadSaturation

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev A : Type := N13IntegralModelContraction.IntegralRing
abbrev K : Type := N13IntegralFractionalHull.FunctionField

local instance integralRationalAlgebra :
    Algebra A N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing A K :=
  N13IntegralFractionalHull.functionField_isFractionRing

abbrev Frac : Type := FractionalIdeal A⁰ K

/-- The product of two vertically saturated integral ideals is vertically
saturated when the first ideal is invertible in the common function field.

The inverse fractional ideal supplies a finite dual-basis-free cancellation:
an element of the first ideal is tested after multiplication by every inverse
section.  Each resulting integral element lies in the second ideal by scalar
saturation, and multiplying the first ideal back recovers product
membership. -/
theorem mul_scalar_saturated_of_left_isUnit
    (I J : Ideal A)
    (hunit : IsUnit (I : Frac))
    (hI :
      ∀ (r : R₂), r ≠ 0 → ∀ a : A,
        algebraMap R₂ A r * a ∈ I → a ∈ I)
    (hJ :
      ∀ (r : R₂), r ≠ 0 → ∀ a : A,
        algebraMap R₂ A r * a ∈ J → a ∈ J) :
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ I * J → a ∈ I * J := by
  intro r hr a hra
  have haI : a ∈ I :=
    hI r hr a (Ideal.mul_le_left hra)
  let U : Fracˣ := hunit.unit
  have hU : (U : Frac) = (I : Frac) := hunit.unit_spec
  have hUinv_mul : (↑U⁻¹ : Frac) * (I : Frac) = 1 := by
    rw [← hU]
    exact Units.inv_mul U
  have hU_mul_inv : (I : Frac) * (↑U⁻¹ : Frac) = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  have hInvSpan :
      (↑U⁻¹ : Frac) *
          FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) ≤
        (J : Frac) := by
    rw [mul_comm, FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have haFrac : algebraMap A K a ∈ (I : Frac) :=
      FractionalIdeal.mem_coeIdeal_of_mem A⁰ haI
    have hzaOne : z * algebraMap A K a ∈ (1 : Frac) := by
      rw [← hUinv_mul]
      exact FractionalIdeal.mul_mem_mul hz haFrac
    have hzaTop :
        z * algebraMap A K a ∈ ((⊤ : Ideal A) : Frac) := by
      simpa using hzaOne
    obtain ⟨c, -, hc⟩ :=
      (FractionalIdeal.mem_coeIdeal A⁰).mp hzaTop
    have hraFrac :
        algebraMap A K (algebraMap R₂ A r * a) ∈
          (I : Frac) * (J : Frac) := by
      rw [← FractionalIdeal.coeIdeal_mul]
      exact FractionalIdeal.mem_coeIdeal_of_mem A⁰ hra
    have hzra :
        z * algebraMap A K (algebraMap R₂ A r * a) ∈
          (J : Frac) := by
      have hmul := FractionalIdeal.mul_mem_mul hz hraFrac
      rw [← mul_assoc, hUinv_mul, one_mul] at hmul
      exact hmul
    have hmaprc :
        algebraMap A K (algebraMap R₂ A r * c) ∈
          (J : Frac) := by
      convert hzra using 1
      rw [map_mul, map_mul, hc]
      ring
    have hrc : algebraMap R₂ A r * c ∈ J := by
      obtain ⟨d, hd, hdc⟩ :=
        (FractionalIdeal.mem_coeIdeal A⁰).mp hmaprc
      have hdc' : d = algebraMap R₂ A r * c :=
        (IsFractionRing.injective A K) hdc
      rw [← hdc']
      exact hd
    have hcJ : c ∈ J := hJ r hr c hrc
    have hmapcJ : algebraMap A K c ∈ (J : Frac) :=
      FractionalIdeal.mem_coeIdeal_of_mem A⁰ hcJ
    convert hmapcJ using 1
    rw [hc]
    ring
  have hspan :
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) ≤
        (I : Frac) * (J : Frac) := by
    calc
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) =
          1 * FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) := by
            rw [one_mul]
      _ = ((I : Frac) * (↑U⁻¹ : Frac)) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) := by
          rw [hU_mul_inv]
      _ = (I : Frac) *
            ((↑U⁻¹ : Frac) *
              FractionalIdeal.spanSingleton A⁰ (algebraMap A K a)) := by
          rw [mul_assoc]
      _ ≤ (I : Frac) * (J : Frac) :=
        mul_le_mul_right hInvSpan (I : Frac)
  have haFracProd : algebraMap A K a ∈ (I : Frac) * (J : Frac) :=
    hspan (FractionalIdeal.mem_spanSingleton_self A⁰ (algebraMap A K a))
  rw [← FractionalIdeal.coeIdeal_mul] at haFracProd
  obtain ⟨b, hb, hba⟩ :=
    (FractionalIdeal.mem_coeIdeal A⁰).mp haFracProd
  have hba' : b = a := (IsFractionRing.injective A K) hba
  simpa [hba'] using hb

/-- Tensoring two vertically saturated two-chart lines preserves vertical
saturation on the affine chart.  Invertibility of the first affine ideal is
the essential hypothesis supplied by the line structure. -/
theorem affineVerticallySaturated_tensor
    (L M : N13TwoChartPicardRealization.Line)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L)
    (hM : N13TwoChartPicardRealization.AffineVerticallySaturated M) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor L M) := by
  change
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ L.affineIdeal * M.affineIdeal →
        a ∈ L.affineIdeal * M.affineIdeal
  exact
    mul_scalar_saturated_of_left_isUnit
      L.affineIdeal M.affineIdeal L.affine_isUnit hL hM

/-- Every valuation-independent point line is vertically saturated on the
ordinary affine chart. -/
theorem pointLine_affineVerticallySaturated
    (x y : N13QuadraticTwoChartSpread.Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13QuadraticTwoChartSpread.pointLine x y hcurve) := by
  rw [N13QuadraticTwoChartSpread.pointLine]
  split
  · let P : N13IntegralAffinePointSpread.IntegralPoint :=
      N13ProperCurveReduction.integralAffineLift x y ‹‖x‖ ≤ 1› hcurve
    change
      N13TwoChartPicardRealization.AffineVerticallySaturated
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)
    exact
      N13IntegralPointPicardRealization.integralPointTwoChartLine_affineVerticallySaturated P
  · exact
      N13EscapingPointPicardRealization.nonintegralPointLine_affineVerticallySaturated
        x y _ hcurve

/-- Tensoring the proper lines of two affine points preserves vertical
saturation.  This covers both split secants and repeated-root tangents. -/
theorem pairLine_affineVerticallySaturated
    (x₁ y₁ x₂ y₂ : N13QuadraticTwoChartSpread.Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂) := by
  change
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor
        (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)
        (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂))
  exact
    affineVerticallySaturated_tensor _ _
      (pointLine_affineVerticallySaturated x₁ y₁ hcurve₁)
      (pointLine_affineVerticallySaturated x₂ y₂ hcurve₂)

end

end MazurProof.N13QuadraticTwoChartSpreadSaturation


