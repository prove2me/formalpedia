-- Prove2me | Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
-- name    : HuangN13_PairLineSpecialRestrictionCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:13:03.56899+00:00
-- url     : https://prove2.me/theorems/3bc997ef-2d50-48cc-9e47-f7880dce4b36
-- title:
--   Actual pair lines and their reduced special divisors
-- statement:
--   The original valuation-independent point and pair lines and their reduced point/pair divisors, with exactly the construction dependencies used in the two restriction identities.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_HuangN13_N13FiniteAffineTwoChart_infinityClosure_isUnit_of_finite
import Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_integralPointIdeal_quotient_finite
import Theorems.Thm_MazurProof_N13IntegralGraphJacobian_graphIdeal_isUnit
import Theorems.Thm_MazurProof_N13IntegralGraphJacobian_mumfordIdeal_isUnit_of_jacobianBezout
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointIdeal_isUnit

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphJacobian
noncomputable section
open N13GeneralizedMumfordIntegral
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Every integral N13 Mumford graph ideal is invertible.  The proof is
the explicit graph dual frame together with the global Jacobian
certificate above. -/
theorem mumfordIdeal_isUnit
    (D : SemiMumford₂) :
    IsUnit
      ((mumfordIdeal D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    exists_jacobian_bezout
  exact
    mumfordIdeal_isUnit_of_jacobianBezout
      D a b hBez
end
end MazurProof.N13IntegralGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralAffinePointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine point graph is already an invertible integral fractional
ideal; no divisorial hull is needed for tensor products of point spreads. -/
theorem pointIdeal_isUnit (P : IntegralPoint) :
    IsUnit
      (pointIdeal P :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      (integralSemiGraph P)
end
end MazurProof.N13IntegralAffinePointSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineCoeffMap_C (r : R₂) :
    affineCoeffMap (C r) = coefficientToInfinityOverlap r := by
  simp [affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineCoeffMap_X :
    affineCoeffMap X = xOverlap := by
  simp [affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClassHom (p : R₂[X]) :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      affineCoeffMap p :=
  affineToInfinityOverlap_of p
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_generalized_yClass :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      affineYImage :=
  affineToInfinityOverlap_yClass
end
end MazurProof.N13OrdinaryCurveOverlap
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
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
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
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restricting the contracted infinity closure back to `D(t)` recovers the
localized affine ideal exactly. -/
theorem map_infinityClosure
    (I : Ideal AffineCurve) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (infinityClosure I) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
  simpa [infinityClosure] using
    (IsLocalization.map_under
      (R := InfinityCurve)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      InfinityOverlap
      (Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I))
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
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- An invertible affine divisor with finite support has an invertible
closure on the ordinary infinity chart.

The finite quotient supplies a monic equation for the affine coordinate.
After reflection, that equation makes `t` a unit modulo the infinity
closure; invertibility on `D(t)` then patches across `t = 0`. -/
theorem infinityClosure_isUnit_of_finite
    (I : Ideal AffineCurve)
    (hI : IsUnit (I : AffineFractionalIdeal))
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    IsUnit
      (infinityClosure I : InfinityFractionalIdeal) := by
  exact HuangN13.N13FiniteAffineTwoChart.infinityClosure_isUnit_of_finite I hI hfinite
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
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The contracted infinity closure and an invertible affine ideal assemble
to a proper line on the two ordinary charts. -/
def twoChartLineOfInfinityClosure
    (I : Ideal AffineCurve)
    (hI : IsUnit (I : AffineFractionalIdeal))
    (hfinite : Module.Finite R₂ (AffineCurve ⧸ I)) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := I
  infinityIdeal := infinityClosure I
  affine_isUnit := hI
  infinity_isUnit :=
    infinityClosure_isUnit_of_finite I hI hfinite
  overlap_eq := (map_infinityClosure I).symm
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
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
/-- An integral affine point has an actual proper two-chart line, obtained
by closing its literal affine graph ideal through the ordinary overlap. -/
def integralPointTwoChartLine
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    N13IntegralInfinityPointSpread.TwoChartLine :=
  twoChartLineOfInfinityClosure
    (N13IntegralAffinePointSpread.pointIdeal P)
    (N13IntegralAffinePointSpread.pointIdeal_isUnit P)
    (integralPointIdeal_quotient_finite P)
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
/-- Points of the six-point special curve. -/
abbrev SpecialCurvePoint : Type :=
  N13RationalPointEndgame.SpecialCurvePoint
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
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- Coefficientwise reduction of an integral affine point.

The good-model equation is preserved by the residue map
`ℤ₂ → 𝔽₂`, so the two reduced coordinates define an affine point of the
special curve. -/
def reducedPoint (P : IntegralPoint) : SpecialCurvePoint :=
  Sum.inl
    ⟨(PadicInt.toZMod P.1.1, PadicInt.toZMod P.1.2),
      by
        simpa [N13GoodModelTwo.AffineEquation,
          N13GoodModelTwo.h, N13GoodModelTwo.rhs] using
          congrArg (PadicInt.toZMod (p := 2)) P.2⟩
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
/-- Proper lines presented on the ordinary affine and infinity charts. -/
abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Proper point line for a point whose affine horizontal coordinate is
integral. -/
def integralPointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    TwoChartLine :=
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  N13FiniteAffineTwoChart.integralPointTwoChartLine P
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Proper point line for an affine point escaping the integral affine
chart. -/
def escapingPointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    TwoChartLine :=
  N13IntegralInfinityPointSpread.nonintegralPointLine
    x y hx hcurve
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Valuation-independent proper line for any two-adic affine curve point. -/
def pointLine
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    TwoChartLine :=
  if hx : ‖x‖ ≤ 1 then
    integralPointLine x y hcurve hx
  else
    escapingPointLine x y hcurve
      (lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx))
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Tensor product of the proper lines attached to two affine points. -/
def pairLine
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    TwoChartLine :=
  N13TwoChartLineTensor.tensor
    (pointLine x₁ y₁ hcurve₁)
    (pointLine x₂ y₂ hcurve₂)
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
/-- Completed points of the six-point special fibre. -/
abbrev SpecialPoint : Type :=
  N13SpecialDivisorCharts.CurvePoint
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Proper reduction of an arbitrary two-adic affine point.

An integral horizontal coordinate is reduced on the ordinary affine chart.
Otherwise its inverse coordinate is integral and the point reduces on the
infinity chart.  The two branches exactly mirror the definition of
`N13QuadraticTwoChartSpread.pointLine`. -/
def reducedPoint
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    SpecialPoint :=
  if hx : ‖x‖ ≤ 1 then
    N13IntegralAffinePointSpecialClass.reducedPoint
      (N13ProperCurveReduction.integralAffineLift x y hx hcurve)
  else
    N13ProperCurveReduction.reduceNonintegralAffine
      x y
      (lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx))
      hcurve
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The literal degree-two special divisor obtained by reducing two affine
points, with multiplicity retained when the two points coincide. -/
def reducedPairDivisor
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  s(reducedPoint x₁ y₁ hcurve₁, reducedPoint x₂ y₂ hcurve₂)
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end


