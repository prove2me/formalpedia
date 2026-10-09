-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphJacobian_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphJacobian_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:36:59.857514+00:00
-- url     : https://prove2.me/theorems/2a04e908-899d-46a2-9348-c767a307c6c3
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityGraphJacobian source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityGraphJacobian

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityGraphJacobian
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDualFrame_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityPointSpread_p0

set_option autoImplicit false




/-!
# Integral graph ideals on the N13 infinity chart

The ordinary infinity chart has equation

`v² + (1 + t² + t³)v = t + t²`.

An explicit integral Bézout certificate for its two relative Jacobian
rows has the odd value `117`.  Hence the rows generate one over the
two-adic integers, and the general graph-Jacobian dual frame makes every
nondegenerate integral polynomial graph on this chart invertible.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityGraphJacobian

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev Base : Type :=
  N13IntegralInfinityChart.Base

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev FunctionField : Type :=
  FractionRing InfinityCurve

abbrev InfinityFractionalIdeal : Type :=
  FractionalIdeal InfinityCurve⁰ FunctionField

def xClassHom : Base →+* InfinityCurve :=
  N13IntegralInfinityPointSpread.xClassHom

def yClass : InfinityCurve :=
  N13IntegralInfinityPointSpread.yClass

abbrev GraphData : Type :=
  GeneralizedGraphIdealCore.SemiGraph
    N13IntegralInfinityChart.hBase
    N13IntegralInfinityChart.rhsBase

/-- The relative ordinate-Jacobian row. -/
def jacobianV : InfinityCurve :=
  2 * yClass +
    xClassHom N13IntegralInfinityChart.hBase

/-- The relative horizontal-Jacobian row. -/
def jacobianT : InfinityCurve :=
  xClassHom (derivative N13IntegralInfinityChart.hBase) *
      yClass -
    xClassHom (derivative N13IntegralInfinityChart.rhsBase)

private theorem derivative_hBase_explicit :
    derivative N13IntegralInfinityChart.hBase =
      (3 : R₂[X]) * X ^ 2 + 2 * X := by
  rw [show (3 : R₂[X]) = C (3 : R₂) by
      exact (map_natCast C 3).symm,
    show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.hBase,
    derivative_add, derivative_pow]
  ring

private theorem derivative_rhsBase_explicit :
    derivative N13IntegralInfinityChart.rhsBase =
      1 + 2 * X := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.rhsBase,
    derivative_add, derivative_pow]

def bezoutA0 : Base :=
  624 * X ^ 4 + 289 * X ^ 3 - 101 * X ^ 2 +
    1713 * X + 232

def bezoutA1 : Base :=
  -450 * X ^ 2 + 924 * X - 535

def bezoutB0 : Base :=
  -1350 * X ^ 3 - 624 * X ^ 2 - 289 * X + 349

def bezoutB1 : Base :=
  1350 * X ^ 4 + 1102 * X + 1233

def bezoutA : InfinityCurve :=
  (624 * N13IntegralInfinityChart.tClass ^ 4 +
      289 * N13IntegralInfinityChart.tClass ^ 3 -
      101 * N13IntegralInfinityChart.tClass ^ 2 +
      1713 * N13IntegralInfinityChart.tClass + 232) +
    (-450 * N13IntegralInfinityChart.tClass ^ 2 +
      924 * N13IntegralInfinityChart.tClass - 535) * yClass

def bezoutB : InfinityCurve :=
  (-1350 * N13IntegralInfinityChart.tClass ^ 3 -
      624 * N13IntegralInfinityChart.tClass ^ 2 -
      289 * N13IntegralInfinityChart.tClass + 349) +
    (1350 * N13IntegralInfinityChart.tClass ^ 4 +
      1102 * N13IntegralInfinityChart.tClass + 1233) * yClass

/-- The infinity-chart Jacobian certificate.  It is the reciprocal-chart
counterpart of the affine certificate with value `13`. -/
theorem scaled_jacobian_bezout :
    bezoutA * jacobianT + bezoutB * jacobianV =
      (117 : InfinityCurve) := by
  have hcurve :=
    N13IntegralInfinityPointSpread.yClass_relation
  have hX :
      xClassHom X = N13IntegralInfinityChart.tClass :=
    N13IntegralInfinityPointSpread.xClassHom_X
  have h2 :
      xClassHom (2 : Base) = (2 : InfinityCurve) :=
    map_natCast xClassHom 2
  have h3 :
      xClassHom (3 : Base) = (3 : InfinityCurve) :=
    map_natCast xClassHom 3
  have hC2 :
      xClassHom (C (2 : R₂)) = (2 : InfinityCurve) := by
    rw [show C (2 : R₂) = (2 : Base) by
      exact map_natCast C 2]
    exact h2
  have hC3 :
      xClassHom (C (3 : R₂)) = (3 : InfinityCurve) := by
    rw [show C (3 : R₂) = (3 : Base) by
      exact map_natCast C 3]
    exact h3
  simp [jacobianT, jacobianV,
    derivative_hBase_explicit,
    derivative_rhsBase_explicit,
    bezoutA, bezoutB,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    yClass, hX, hC2, hC3] at hcurve ⊢
  linear_combination
    (1350 * N13IntegralInfinityChart.tClass ^ 4 +
      1872 * N13IntegralInfinityChart.tClass ^ 3 +
      243 * N13IntegralInfinityChart.tClass ^ 2 +
      1134 * N13IntegralInfinityChart.tClass + 2466) * hcurve

theorem oneHundredSeventeen_isUnit :
    IsUnit (117 : InfinityCurve) := by
  have h : IsUnit (117 : R₂) := by
    rw [PadicInt.isUnit_iff]
    exact
      PadicInt.norm_natCast_eq_one_iff.mpr
        (by norm_num)
  convert h.map
    ((algebraMap Base InfinityCurve).comp
      (Polynomial.C : R₂ →+* Base)) using 1
  exact
    (map_natCast
      ((algebraMap Base InfinityCurve).comp
        (Polynomial.C : R₂ →+* Base)) 117).symm

/-- The two relative Jacobian rows generate one globally on the ordinary
infinity chart. -/
theorem exists_jacobian_bezout :
    ∃ a b : InfinityCurve,
      a * jacobianT + b * jacobianV = 1 := by
  let u : InfinityCurveˣ :=
    oneHundredSeventeen_isUnit.unit
  refine
    ⟨(u⁻¹ : InfinityCurveˣ) * bezoutA,
      (u⁻¹ : InfinityCurveˣ) * bezoutB, ?_⟩
  calc
    (((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
            bezoutA) * jacobianT +
          (((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
            bezoutB) * jacobianV =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
          (bezoutA * jacobianT +
            bezoutB * jacobianV) := by ring
    _ =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) * 117 := by
      rw [scaled_jacobian_bezout]
    _ =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
          (u : InfinityCurve) := by
      rw [oneHundredSeventeen_isUnit.unit_spec]
    _ = 1 := by simp

private theorem derivative_graphData_curve_eq
    (D : GraphData) :
    (C (2 : R₂) * D.v +
          N13IntegralInfinityChart.hBase) *
          derivative D.v +
        derivative N13IntegralInfinityChart.hBase * D.v -
        derivative N13IntegralInfinityChart.rhsBase =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h

private theorem jacobianV_eq_graphData
    (D : GraphData) :
    jacobianV =
      GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v +
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV
              N13IntegralInfinityChart.hBase D.v) := by
  simp only [jacobianV,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    map_neg, map_sub]
  ring

private theorem jacobianT_eq_graphData
    (D : GraphData) :
    jacobianT =
      xClassHom (derivative D.u) * xClassHom D.w +
        xClassHom D.u * xClassHom (derivative D.w) -
        xClassHom (derivative D.v) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV
                N13IntegralInfinityChart.hBase D.v) +
        (xClassHom
              (derivative N13IntegralInfinityChart.hBase) +
            xClassHom (derivative D.v)) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v := by
  have h :=
    congrArg xClassHom
      (derivative_graphData_curve_eq D)
  have htwo :
      xClassHom (C (2 : R₂)) =
        (2 : InfinityCurve) := by
    exact map_natCast xClassHom 2
  simp only [jacobianT,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    map_add, map_sub, map_neg, map_mul] at h ⊢
  rw [htwo] at h
  linear_combination h

/-- Every nondegenerate integral polynomial graph on the ordinary
infinity chart is invertible. -/
theorem graphIdeal_isUnit
    (D : GraphData)
    (hu : D.u ≠ 0) :
    IsUnit
      ((GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass D.u D.v :
          Ideal InfinityCurve) :
        InfinityFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    exists_jacobian_bezout
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClassHom D.u)
      (G :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v)
      (Gbar :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV
              N13IntegralInfinityChart.hBase D.v))
      (W := xClassHom D.w)
      (Fy := jacobianV)
      (Fx := jacobianT)
      (Ux := xClassHom (derivative D.u))
      (Wx := xClassHom (derivative D.w))
      (Vx := xClassHom (derivative D.v))
      (hx :=
        xClassHom
          (derivative N13IntegralInfinityChart.hBase))
      (a := a) (b := b)
  · change
      N13IntegralInfinityPointSpread.xClassHom D.u ≠ 0
    intro hzero
    apply hu
    apply N13IntegralInfinityPointSpread.xClassHom_injective
    simpa only [map_zero] using hzero
  · exact
      GeneralizedGraphIdealCore.ySubClass_mul_conjugate
        xClassHom yClass
        N13IntegralInfinityChart.hBase
        N13IntegralInfinityChart.rhsBase
        D
        N13IntegralInfinityPointSpread.yClass_relation
  · exact jacobianV_eq_graphData D
  · exact jacobianT_eq_graphData D
  · exact hBez

end

end MazurProof.N13IntegralInfinityGraphJacobian


