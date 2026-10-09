-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphJacobian_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphJacobian_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:50:30.28691+00:00
-- url     : https://prove2.me/theorems/d0865dd8-529f-4265-97c9-1bcda23efb9a
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphJacobian source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphJacobian

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphJacobian
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDecompositionFrame_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0

set_option autoImplicit false




/-!
# Vertical graph ideals on the N13 infinity chart

A rank-two quotient whose integral basis is `{1,v}` is cut out by a monic
relation `m(v)` and a linear equation `t = a + c v`.  Substitution into the
infinity-chart equation produces the complementary factor.  Explicit
divided differences decompose both global Jacobian rows in this vertical
graph frame, so the generic decomposition theorem proves invertibility.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev FunctionField : Type :=
  N13IntegralInfinityGraphJacobian.FunctionField

abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityGraphJacobian.InfinityFractionalIdeal

/-- Substitute a linear expression for `t` in the infinity curve, leaving
`v` as the polynomial variable. -/
def verticalCurve (s : R₂[X]) : R₂[X] :=
  X ^ 2 +
    N13IntegralInfinityChart.hBase.comp s * X -
    N13IntegralInfinityChart.rhsBase.comp s

/-- Integral vertical graph data `m(v)=0`, `t=a+cv`. -/
structure VerticalGraph where
  m : R₂[X]
  a : R₂
  c : R₂
  w : R₂[X]
  m_monic : m.Monic
  curve_eq :
    verticalCurve (C a + C c * X) = m * w

namespace VerticalGraph

def s (E : VerticalGraph) : R₂[X] :=
  C E.a + C E.c * X

def ideal (E : VerticalGraph) : Ideal InfinityCurve :=
  Ideal.span
    ({aeval N13IntegralInfinityGraphJacobian.yClass E.m,
      N13IntegralInfinityChart.tClass -
        aeval N13IntegralInfinityGraphJacobian.yClass E.s} :
      Set InfinityCurve)

end VerticalGraph

open N13IntegralInfinityGraphJacobian

private theorem xClassHom_X :
    xClassHom X = N13IntegralInfinityChart.tClass := by
  rfl

def L (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.s

def U (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.m

def G (E : VerticalGraph) : InfinityCurve :=
  N13IntegralInfinityChart.tClass - L E

def W (E : VerticalGraph) : InfinityCurve :=
  aeval yClass E.w

/-- Divided-difference cofactor for
`F(t,v) - F(L,v) = (t-L) Gbar`. -/
def Gbar (E : VerticalGraph) : InfinityCurve :=
  yClass *
      (N13IntegralInfinityChart.tClass ^ 2 +
        N13IntegralInfinityChart.tClass * L E +
        L E ^ 2) +
    (yClass - 1) *
      (N13IntegralInfinityChart.tClass + L E) -
    1

def GbarT (E : VerticalGraph) : InfinityCurve :=
  yClass *
      (2 * N13IntegralInfinityChart.tClass + L E) +
    (yClass - 1)

def GbarV (E : VerticalGraph) : InfinityCurve :=
  N13IntegralInfinityChart.tClass ^ 2 +
      N13IntegralInfinityChart.tClass * L E +
      L E ^ 2 +
      (N13IntegralInfinityChart.tClass + L E) +
    algebraMap R₂ InfinityCurve E.c *
      (yClass *
          (N13IntegralInfinityChart.tClass + 2 * L E) +
        (yClass - 1))

def Uv (E : VerticalGraph) : InfinityCurve :=
  aeval yClass (derivative E.m)

def Wv (E : VerticalGraph) : InfinityCurve :=
  aeval yClass (derivative E.w)

theorem verticalCurve_eval
    (E : VerticalGraph) :
    yClass ^ 2 +
          (1 + L E ^ 2 + L E ^ 3) * yClass -
        (L E + L E ^ 2) =
      U E * W E := by
  have h :=
    congrArg (aeval yClass) E.curve_eq
  simpa [verticalCurve, VerticalGraph.s, L, U, W,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    aeval_comp] using h

theorem curve_eval :
    yClass ^ 2 +
          (1 + N13IntegralInfinityChart.tClass ^ 2 +
              N13IntegralInfinityChart.tClass ^ 3) * yClass -
        (N13IntegralInfinityChart.tClass +
          N13IntegralInfinityChart.tClass ^ 2) =
      0 := by
  have h :
      yClass ^ 2 +
          xClassHom N13IntegralInfinityChart.hBase * yClass =
        xClassHom N13IntegralInfinityChart.rhsBase := by
    exact N13IntegralInfinityPointSpread.yClass_relation
  simp only [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase, map_add, map_pow, map_one,
    xClassHom_X] at h
  exact sub_eq_zero.mpr h

/-- Exact complementary factorization in the infinity coordinate ring. -/
theorem G_mul_Gbar
    (E : VerticalGraph) :
    G E * Gbar E = -(U E * W E) := by
  have ht := curve_eval
  have hL := verticalCurve_eval E
  dsimp only [G, Gbar]
  linear_combination ht - hL

private theorem derivative_hBase :
    derivative N13IntegralInfinityChart.hBase =
      2 * X + 3 * X ^ 2 := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm,
    show (3 : R₂[X]) = C (3 : R₂) by
      exact (map_natCast C 3).symm]
  simp [N13IntegralInfinityChart.hBase,
    derivative_add, derivative_pow]

private theorem derivative_rhsBase :
    derivative N13IntegralInfinityChart.rhsBase =
      1 + 2 * X := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.rhsBase,
    derivative_add, derivative_pow]

theorem jacobianT_explicit :
    jacobianT =
      yClass *
          (2 * N13IntegralInfinityChart.tClass +
            3 * N13IntegralInfinityChart.tClass ^ 2) -
        (1 + 2 * N13IntegralInfinityChart.tClass) := by
  have h2 :
      xClassHom (2 : R₂[X]) = (2 : InfinityCurve) :=
    map_natCast xClassHom 2
  have h3 :
      xClassHom (3 : R₂[X]) = (3 : InfinityCurve) :=
    map_natCast xClassHom 3
  rw [jacobianT, derivative_hBase, derivative_rhsBase]
  simp only [map_add, map_mul, map_pow, map_one]
  rw [h2, h3, xClassHom_X]
  ring

theorem jacobianV_explicit :
    jacobianV =
      2 * yClass +
        1 + N13IntegralInfinityChart.tClass ^ 2 +
          N13IntegralInfinityChart.tClass ^ 3 := by
  simp only [jacobianV, N13IntegralInfinityChart.hBase,
    map_add, map_pow, map_one, xClassHom_X]
  ring

theorem jacobianT_decomposition
    (E : VerticalGraph) :
    jacobianT = G E * GbarT E + Gbar E := by
  rw [jacobianT_explicit]
  simp only [G, GbarT, Gbar]
  ring

private theorem derivative_verticalCurve
    (E : VerticalGraph) :
    algebraMap R₂ InfinityCurve E.c *
          (yClass * (2 * L E + 3 * L E ^ 2) -
            (1 + 2 * L E)) +
        (2 * yClass + 1 + L E ^ 2 + L E ^ 3) =
      U E * Wv E + W E * Uv E := by
  have hder :=
    congrArg derivative E.curve_eq
  have h :=
    congrArg (aeval yClass) hder
  simp only [verticalCurve, derivative_sub, derivative_add,
    derivative_mul, derivative_pow, derivative_X,
    derivative_comp, derivative_C, zero_add, zero_mul,
    map_sub, map_add, map_mul, map_pow, map_one,
    aeval_X, aeval_comp, Polynomial.aeval_C] at h
  rw [derivative_hBase, derivative_rhsBase] at h
  simp only [map_add, map_mul, map_pow, map_one, aeval_X] at h
  norm_num only [map_ofNat] at h
  change
    algebraMap R₂ InfinityCurve E.c *
          (yClass * (2 * L E + 3 * L E ^ 2) -
            (1 + 2 * L E)) +
        (2 * yClass + 1 + L E ^ 2 + L E ^ 3) =
      U E * Wv E + W E * Uv E
  dsimp only [L, U, W, Uv, Wv, VerticalGraph.s]
  simp [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] at h
  simp only [map_add, map_mul, Polynomial.aeval_C, aeval_X]
  linear_combination h

theorem jacobianV_decomposition
    (E : VerticalGraph) :
    jacobianV =
      G E * GbarV E +
        U E * Wv E +
        W E * Uv E +
        Gbar E * (-algebraMap R₂ InfinityCurve E.c) := by
  have hder := derivative_verticalCurve E
  rw [jacobianV_explicit]
  dsimp only [G, GbarV, Gbar]
  linear_combination hder

private theorem algebraMap_eq_baseClass_C
    (r : R₂) :
    algebraMap R₂ InfinityCurve r =
      N13IntegralInfinityReduction.integralBaseClass (C r) := by
  rfl

theorem G_ne_zero
    (E : VerticalGraph) :
    G E ≠ 0 := by
  intro hzero
  have hcoeff :=
    congrArg N13IntegralInfinityReduction.integralCoeff0 hzero
  simp only [G, L, VerticalGraph.s, map_sub, map_add, map_mul,
    Polynomial.aeval_C, aeval_X, map_zero] at hcoeff
  rw [algebraMap_eq_baseClass_C E.a,
    algebraMap_eq_baseClass_C E.c] at hcoeff
  rw [show
      N13IntegralInfinityChart.tClass =
        N13IntegralInfinityReduction.integralBaseClass X by rfl,
    show yClass = N13IntegralInfinityChart.vClass by rfl] at hcoeff
  simp only [map_sub, map_add,
    N13IntegralInfinityReduction.integralCoeff0_baseClass,
    N13IntegralInfinityReduction.integralCoeff0_baseClass_mul_vClass,
    sub_zero] at hcoeff
  have hcoeffOne :=
    congrArg (fun p : R₂[X] => p.coeff 1) hcoeff
  simpa using hcoeffOne

/-- Every nondegenerate recovered vertical graph on the ordinary infinity
chart is an invertible fractional ideal. -/
theorem verticalIdeal_isUnit
    (E : VerticalGraph) :
    IsUnit
      ((E.ideal : Ideal InfinityCurve) :
        InfinityFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    exists_jacobian_bezout
  have hrelation :
      U E * W E = -(G E * Gbar E) := by
    have h := G_mul_Gbar E
    linear_combination h
  have hT :
      jacobianT =
        G E * GbarT E +
          U E * 0 + W E * 0 + Gbar E * 1 := by
    rw [jacobianT_decomposition]
    ring
  have hV :
      jacobianV =
        G E * GbarV E +
          U E * Wv E +
          W E * Uv E +
          Gbar E * (-algebraMap R₂ InfinityCurve E.c) :=
    jacobianV_decomposition E
  have hunit :=
    GraphJacobianDecompositionFrame.graphJacobian_isUnit_of_decompositions
      (K := FunctionField)
      (U := G E) (G := U E) (H := W E) (W := Gbar E)
      (Fx := jacobianT) (Fy := jacobianV)
      (αx := GbarT E) (βx := 0) (γx := 0) (δx := 1)
      (αy := GbarV E) (βy := Wv E)
      (γy := Uv E)
      (δy := -algebraMap R₂ InfinityCurve E.c)
      (a := a) (b := b)
      (G_ne_zero E) hrelation hT hV hBez
  have hideal :
      E.ideal = Ideal.span ({G E, U E} : Set InfinityCurve) := by
    apply congrArg Ideal.span
    ext z
    simp [VerticalGraph.ideal, U, G, L, or_comm]
  rw [hideal]
  exact hunit

end

end MazurProof.N13IntegralInfinityVerticalGraphJacobian


