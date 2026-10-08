-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:17:12.848315+00:00
-- url     : https://prove2.me/theorems/c84f50b0-d5e9-4696-b49d-c58cf96d7617
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralGraphJacobian source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralGraphJacobian

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralGraphJacobian
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDualFrame_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GeneralizedGraphIdealCore_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0

set_option autoImplicit false




/-!
# Integral N13 graph ideals and the affine Jacobian

This file instantiates the generic graph-Jacobian dual frame for the good
integral N13 equation.  A short resultant certificate proves that the two
relative Jacobian rows generate one globally, so every integral Mumford
graph ideal is invertible.  No fixed special graph or point classification
is used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphJacobian

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.SemiMumford
    (R := R₂)

local instance integralRingDomain :
    IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

open N13GeneralizedMumfordIntegral

/-- The relative `Y`-Jacobian row of
`Y² + h(X)Y - rhs(X)`. -/
def jacobianY : IntegralRing :=
  2 * yClass +
    xClass (hPoly (R := R₂))

/-- The relative `X`-Jacobian row of
`Y² + h(X)Y - rhs(X)`. -/
def jacobianX : IntegralRing :=
  xClass (derivative (hPoly (R := R₂))) *
      yClass -
    xClass (derivative (rhsPoly (R := R₂)))

private theorem derivative_hPoly_explicit :
    derivative (hPoly (R := R₂)) =
      (3 : R₂[X]) * X ^ 2 + 1 := by
  simp [hPoly, derivative_add, derivative_pow]
  exact map_natCast C 3

private theorem derivative_rhsPoly_explicit :
    derivative (rhsPoly (R := R₂)) =
      (5 : R₂[X]) * X ^ 4 +
        (4 : R₂[X]) * X ^ 3 := by
  simp [rhsPoly, derivative_add, derivative_pow]
  congr 1

private theorem derivative_curve_eq
    (D : SemiMumford₂) :
    (C (2 : R₂) * D.v + hPoly) *
          derivative D.v +
          derivative hPoly * D.v -
        derivative rhsPoly =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h

/-- The `Y`-Jacobian row is the sum of the graph function and its
hyperelliptic conjugate. -/
theorem jacobianY_eq_graph_add_conjugate
    (D : SemiMumford₂) :
    jacobianY =
      ySubClass D.v +
        ySubClass (conjugateV D.v) := by
  simp only [jacobianY, ySubClass, conjugateV,
    xClass_neg, xClass_sub]
  ring

/-- Differentiating the integral Mumford equation decomposes the
`X`-Jacobian row along the two graph generators. -/
theorem jacobianX_eq_graph_decomposition
    (D : SemiMumford₂) :
    jacobianX =
      xClass (derivative D.u) * xClass D.w +
        xClass D.u * xClass (derivative D.w) -
        xClass (derivative D.v) *
          ySubClass (conjugateV D.v) +
        (xClass (derivative hPoly) +
            xClass (derivative D.v)) *
          ySubClass D.v := by
  have h :=
    congrArg
      (xClass (R := R₂))
      (derivative_curve_eq D)
  have htwo :
      xClass (R := R₂) (C (2 : R₂)) =
        (2 : IntegralRing) := by
    rw [show C (2 : R₂) = (2 : R₂[X]) by
      exact map_natCast C 2]
    exact xClass_natCast 2
  simp only [jacobianX, ySubClass, conjugateV,
    xClass_add, xClass_sub, xClass_neg,
    xClass_mul] at h ⊢
  rw [htwo] at h
  linear_combination h

/-- The first coordinate-ring coefficient of the Jacobian Bézout
certificate. -/
def bezoutA : IntegralRing :=
  (30 * xClass X ^ 5 + 97 * xClass X ^ 4 +
      92 * xClass X ^ 3 + 50 * xClass X + 31) +
    (10 * xClass X ^ 2 + 30 * xClass X - 3) *
      yClass

/-- The second coordinate-ring coefficient of the Jacobian Bézout
certificate. -/
def bezoutB : IntegralRing :=
  (63 * xClass X ^ 5 + 153 * xClass X ^ 4 +
      98 * xClass X ^ 3 + 13 * xClass X ^ 2 -
      13 * xClass X + 13) +
    (60 * xClass X ^ 4 + 151 * xClass X ^ 3 +
      151 * xClass X ^ 2 - 63 * xClass X + 60) *
      yClass

/-- The integral resultant certificate for the two relative Jacobian
rows.  It comes from the univariate Euclidean identity between
`h² + 4 * rhs` and `h' * h + 2 * rhs'`; its right-hand side is the
optimal odd scalar `13`. -/
theorem scaled_jacobian_bezout :
    bezoutA * jacobianX + bezoutB * jacobianY =
      (13 : IntegralRing) := by
  have hcurve :=
    yClass_relation (R := R₂)
  simp only [jacobianX, derivative_hPoly_explicit,
    derivative_rhsPoly_explicit, xClass_add,
    xClass_mul, xClass_pow]
  have h3 :
      xClass (R := R₂) (3 : R₂[X]) =
        (3 : IntegralRing) :=
    xClass_natCast 3
  have h4 :
      xClass (R := R₂) (4 : R₂[X]) =
        (4 : IntegralRing) :=
    xClass_natCast 4
  have h5 :
      xClass (R := R₂) (5 : R₂[X]) =
        (5 : IntegralRing) :=
    xClass_natCast 5
  rw [h3, h4, h5]
  simp [bezoutA, bezoutB, jacobianY,
    hPoly, rhsPoly] at hcurve ⊢
  linear_combination
    (150 * xClass (R := R₂) X ^ 4 +
      392 * xClass (R := R₂) X ^ 3 +
      303 * xClass (R := R₂) X ^ 2 -
      96 * xClass (R := R₂) X + 117) * hcurve

/-- The odd resultant scalar in the Jacobian certificate is a unit in the
integral coordinate ring. -/
theorem thirteen_isUnit :
    IsUnit (13 : IntegralRing) := by
  have h : IsUnit (13 : R₂) := by
    rw [PadicInt.isUnit_iff]
    exact
      PadicInt.norm_natCast_eq_one_iff.mpr
        (by norm_num)
  convert h.map (algebraMap R₂ IntegralRing) using 1
  exact
    (map_natCast (algebraMap R₂ IntegralRing) 13).symm

/-- The two relative Jacobian rows generate the unit ideal globally over
the integral N13 model. -/
theorem exists_jacobian_bezout :
    ∃ a b : IntegralRing,
      a * jacobianX + b * jacobianY = 1 := by
  let u : IntegralRingˣ :=
    thirteen_isUnit.unit
  refine
    ⟨(u⁻¹ : IntegralRingˣ) * bezoutA,
      (u⁻¹ : IntegralRingˣ) * bezoutB, ?_⟩
  calc
    (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutA) * jacobianX +
          (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutB) * jacobianY =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (bezoutA * jacobianX +
            bezoutB * jacobianY) := by ring
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) * 13 := by
      rw [scaled_jacobian_bezout]
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (u : IntegralRing) := by
      rw [thirteen_isUnit.unit_spec]
    _ = 1 := by simp

/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/

abbrev GraphData : Type :=
  GeneralizedGraphIdealCore.SemiGraph
    (hPoly (R := R₂)) (rhsPoly (R := R₂))

private theorem derivative_graphData_curve_eq
    (D : GraphData) :
    (C (2 : R₂) * D.v + hPoly) *
          derivative D.v +
          derivative hPoly * D.v -
        derivative rhsPoly =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h

private theorem jacobianY_eq_graphData
    (D : GraphData) :
    jacobianY =
      GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v +
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV hPoly D.v) := by
  simp only [jacobianY, GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    xClassHom_apply, xClass_neg, xClass_sub]
  ring

private theorem jacobianX_eq_graphData
    (D : GraphData) :
    jacobianX =
      xClass (derivative D.u) * xClass D.w +
        xClass D.u * xClass (derivative D.w) -
        xClass (derivative D.v) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV hPoly D.v) +
        (xClass (derivative hPoly) +
            xClass (derivative D.v)) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v := by
  have h :=
    congrArg
      (xClass (R := R₂))
      (derivative_graphData_curve_eq D)
  have htwo :
      xClass (R := R₂) (C (2 : R₂)) =
        (2 : IntegralRing) := by
    rw [show C (2 : R₂) = (2 : R₂[X]) by
      exact map_natCast C 2]
    exact xClass_natCast 2
  simp only [jacobianX,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    xClassHom_apply, xClass_add, xClass_sub, xClass_neg,
    xClass_mul] at h ⊢
  rw [htwo] at h
  linear_combination h

/-- Every nondegenerate integral polynomial graph on the affine good model
is invertible.  Its horizontal equation need not be monic. -/
theorem graphIdeal_isUnit
    (D : GraphData)
    (hu : D.u ≠ 0) :
    IsUnit
      ((GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ := exists_jacobian_bezout
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClass D.u)
      (G :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v)
      (Gbar :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV hPoly D.v))
      (W := xClass D.w)
      (Fy := jacobianY)
      (Fx := jacobianX)
      (Ux := xClass (derivative D.u))
      (Wx := xClass (derivative D.w))
      (Vx := xClass (derivative D.v))
      (hx := xClass (derivative hPoly))
      (a := a) (b := b)
  · intro hzero
    apply hu
    have hcoeff :=
      congrArg (coeff0 (R := R₂)) hzero
    simpa only [coeff0_xClass, map_zero] using hcoeff
  · exact
      GeneralizedGraphIdealCore.ySubClass_mul_conjugate
        xClassHom yClass hPoly rhsPoly D
        (yClass_relation (R := R₂))
  · exact jacobianY_eq_graphData D
  · exact jacobianX_eq_graphData D
  · exact hBez

/-- A global relative-Jacobian Bézout pair makes every integral smooth
Mumford graph invertible by the explicit graph dual frame. -/
theorem mumfordIdeal_isUnit_of_jacobianBezout
    (D : SemiMumford₂)
    (a b : IntegralRing)
    (hBez :
      a * jacobianX + b * jacobianY = 1) :
    IsUnit
      ((mumfordIdeal D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClass D.u)
      (G := ySubClass D.v)
      (Gbar := ySubClass (conjugateV D.v))
      (W := xClass D.w)
      (Fy := jacobianY)
      (Fx := jacobianX)
      (Ux := xClass (derivative D.u))
      (Wx := xClass (derivative D.w))
      (Vx := xClass (derivative D.v))
      (hx := xClass (derivative hPoly))
      (a := a) (b := b)
  · intro hzero
    apply D.u_monic.ne_zero
    have hcoeff :=
      congrArg (coeff0 (R := R₂)) hzero
    simpa only [coeff0_xClass, map_zero] using hcoeff
  · exact ySubClass_mul_conjugate D
  · exact jacobianY_eq_graph_add_conjugate D
  · exact jacobianX_eq_graph_decomposition D
  · exact hBez

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


