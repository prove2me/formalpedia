-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13VerticalGraphJacobian_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13VerticalGraphJacobian_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:10:23.542616+00:00
-- url     : https://prove2.me/theorems/9ef62088-6c27-4540-8dc6-d3669e48c3ea
-- title:
--   FLT.Assumptions.MazurProof.N13VerticalGraphJacobian source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13VerticalGraphJacobian

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13VerticalGraphJacobian
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDecompositionFrame_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalGraphRecovery_p0

set_option autoImplicit false




open Polynomial
open scoped nonZeroDivisors

/-!
# The vertical graph Jacobian frame for the N13 integral model

A rank-two contraction with basis `{1, y}` is a vertical graph `x = s(y)`.
Dividing the curve equation by `x - s(y)` supplies the complementary factor.
Together with the differentiated vertical relation, these two factors express both
Jacobian rows in the graph frame. The global Jacobian Bezout identity then makes
the recovered graph ideal invertible.
-/

namespace MazurProof.N13VerticalGraphJacobian

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralGraphJacobian.R₂
abbrev IntegralRing : Type :=
  N13IntegralGraphJacobian.IntegralRing
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev VerticalGraph : Type :=
  N13RankTwoVerticalGraphRecovery.VerticalGraph

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
open N13RankTwoVerticalGraphRecovery

def curveInX : IntegralRing[X] :=
  C (N13ConcreteGraphRecovery.integralY ^ 2) +
    (hPoly (R := R₂)).map (algebraMap R₂ IntegralRing) *
      C N13ConcreteGraphRecovery.integralY -
    (rhsPoly (R := R₂)).map (algebraMap R₂ IntegralRing)

def sValue (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.s

def U (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.m

def G (E : VerticalGraph) : IntegralRing :=
  N13CanonicalContractionQuotient.integralX - sValue E

def W (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.w

def complementPoly (E : VerticalGraph) : IntegralRing[X] :=
  curveInX /ₘ (X - C (sValue E))

def H (E : VerticalGraph) : IntegralRing :=
  (complementPoly E).eval
    N13CanonicalContractionQuotient.integralX

def Hx (E : VerticalGraph) : IntegralRing :=
  (derivative (complementPoly E)).eval
    N13CanonicalContractionQuotient.integralX

def fyPoly : IntegralRing[X] :=
  C (2 * N13ConcreteGraphRecovery.integralY) +
    (hPoly (R := R₂)).map (algebraMap R₂ IntegralRing)

theorem algebraMap_eq_xClass_C (r : R₂) :
    algebraMap R₂ IntegralRing r =
      xClass (R := R₂) (C r) := by
  rfl

theorem curveInX_eval_integralX :
    curveInX.eval
        N13CanonicalContractionQuotient.integralX =
      0 := by
  simp only [curveInX, eval_sub, eval_add, eval_mul,
    eval_C, eval_map]
  change
    N13ConcreteGraphRecovery.integralY ^ 2 +
        aeval N13CanonicalContractionQuotient.integralX
            (hPoly (R := R₂)) *
          N13ConcreteGraphRecovery.integralY -
      aeval N13CanonicalContractionQuotient.integralX
        (rhsPoly (R := R₂)) = 0
  rw [N13ConcreteGraphRecovery.aeval_integralX,
    N13ConcreteGraphRecovery.aeval_integralX]
  exact sub_eq_zero.mpr
    (by
      simpa only [N13ConcreteGraphRecovery.integralY] using
        (N13GeneralizedMumfordIntegral.yClass_relation
          (R := R₂)))

theorem curveInX_eval_sValue
    (E : VerticalGraph) :
    curveInX.eval (sValue E) = U E * W E := by
  have hcurve := congrArg
    (aeval N13ConcreteGraphRecovery.integralY) E.curve_eq
  simp only [verticalCurve, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_comp] at hcurve
  have hs :
      sValue E =
        algebraMap R₂ IntegralRing E.a +
          algebraMap R₂ IntegralRing E.c *
            N13ConcreteGraphRecovery.integralY := by
    simp [sValue, VerticalGraph.s]
  rw [hs]
  simp only [curveInX, eval_sub, eval_add, eval_mul,
    eval_C, eval_map]
  change
    N13ConcreteGraphRecovery.integralY ^ 2 +
          aeval
              (algebraMap R₂ IntegralRing E.a +
                algebraMap R₂ IntegralRing E.c *
                  N13ConcreteGraphRecovery.integralY)
              (hPoly (R := R₂)) *
            N13ConcreteGraphRecovery.integralY -
        aeval
            (algebraMap R₂ IntegralRing E.a +
              algebraMap R₂ IntegralRing E.c *
                N13ConcreteGraphRecovery.integralY)
            (rhsPoly (R := R₂)) =
      U E * W E
  simpa only [U, W, Polynomial.aeval_C] using hcurve

theorem G_mul_H
    (E : VerticalGraph) :
    G E * H E = -(U E * W E) := by
  have hdiv :=
    X_sub_C_mul_divByMonic_eq_sub_modByMonic
      curveInX (sValue E)
  rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
  have heval := congrArg
    (fun p : IntegralRing[X] =>
      p.eval N13CanonicalContractionQuotient.integralX) hdiv
  simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
  rw [curveInX_eval_integralX, curveInX_eval_sValue E,
    zero_sub] at heval
  simpa [G, H, complementPoly] using heval

theorem jacobianX_decomposition
    (E : VerticalGraph) :
    N13IntegralGraphJacobian.jacobianX =
      U E * 0 + G E * Hx E + H E * 1 + W E * 0 := by
  have hder :=
    divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      curveInX (sValue E)
  have heval := congrArg
    (fun p : IntegralRing[X] =>
      p.eval N13CanonicalContractionQuotient.integralX) hder
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]
    at heval
  have hcurveDerivative :
      (derivative curveInX).eval
          N13CanonicalContractionQuotient.integralX =
        N13IntegralGraphJacobian.jacobianX := by
    simp only [curveInX, derivative_add, derivative_sub,
      derivative_mul, derivative_C, zero_add,
      derivative_map, eval_sub, eval_mul,
      eval_map, eval_C, mul_zero, add_zero]
    change
      aeval N13CanonicalContractionQuotient.integralX
          (derivative (hPoly (R := R₂))) *
            N13ConcreteGraphRecovery.integralY -
          aeval N13CanonicalContractionQuotient.integralX
            (derivative (rhsPoly (R := R₂))) =
        N13IntegralGraphJacobian.jacobianX
    rw [N13ConcreteGraphRecovery.aeval_integralX,
      N13ConcreteGraphRecovery.aeval_integralX]
    rfl
  rw [hcurveDerivative] at heval
  calc
    N13IntegralGraphJacobian.jacobianX =
        H E + G E * Hx E := by
      simpa [G, H, Hx, complementPoly] using heval.symm
    _ = U E * 0 + G E * Hx E + H E * 1 + W E * 0 := by
      ring

theorem derivative_verticalCurve_linear
    (a c : R₂) :
    derivative (verticalCurve (C a + C c * X)) =
      C c *
          (((derivative (hPoly (R := R₂))).comp
              (C a + C c * X)) * X -
            (derivative (rhsPoly (R := R₂))).comp
              (C a + C c * X)) +
        (C 2 * X +
          (hPoly (R := R₂)).comp (C a + C c * X)) := by
  simp only [verticalCurve, derivative_sub, derivative_add,
    derivative_mul, derivative_pow, derivative_X,
    derivative_comp, derivative_C, zero_add, zero_mul]
  ring

theorem derivative_curveInX_eval
    (z : IntegralRing) :
    (derivative curveInX).eval z =
      aeval z (derivative (hPoly (R := R₂))) *
          N13ConcreteGraphRecovery.integralY -
        aeval z (derivative (rhsPoly (R := R₂))) := by
  simp only [curveInX, derivative_sub, derivative_add,
    derivative_mul, derivative_C, zero_add,
    derivative_map, eval_sub, eval_mul, eval_map,
    eval_C, mul_zero, add_zero]
  rfl

theorem fyPoly_eval
    (z : IntegralRing) :
    fyPoly.eval z =
      2 * N13ConcreteGraphRecovery.integralY +
        aeval z (hPoly (R := R₂)) := by
  simp [fyPoly, eval_add, eval_C, eval_map]
  rfl

theorem fyPoly_eval_integralX :
    fyPoly.eval
        N13CanonicalContractionQuotient.integralX =
      N13IntegralGraphJacobian.jacobianY := by
  rw [fyPoly_eval,
    N13ConcreteGraphRecovery.aeval_integralX]
  rfl

theorem totalDerivative_at_s
    (E : VerticalGraph) :
    algebraMap R₂ IntegralRing E.c *
          (derivative curveInX).eval (sValue E) +
        fyPoly.eval (sValue E) =
      U E *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.w) +
        W E *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.m) := by
  have hder := congrArg derivative E.curve_eq
  rw [derivative_verticalCurve_linear] at hder
  have heval := congrArg
    (aeval N13ConcreteGraphRecovery.integralY) hder
  simp only [derivative_mul, map_add, map_sub, map_mul,
    aeval_X, aeval_comp, Polynomial.aeval_C] at heval
  rw [derivative_curveInX_eval, fyPoly_eval]
  have hs :
      sValue E =
        algebraMap R₂ IntegralRing E.a +
          algebraMap R₂ IntegralRing E.c *
            N13ConcreteGraphRecovery.integralY := by
    simp [sValue, VerticalGraph.s]
  rw [hs]
  norm_num only [map_ofNat] at heval
  change
    algebraMap R₂ IntegralRing E.c *
          (aeval
                (algebraMap R₂ IntegralRing E.a +
                  algebraMap R₂ IntegralRing E.c *
                    N13ConcreteGraphRecovery.integralY)
                (derivative (hPoly (R := R₂))) *
              N13ConcreteGraphRecovery.integralY -
            aeval
                (algebraMap R₂ IntegralRing E.a +
                  algebraMap R₂ IntegralRing E.c *
                    N13ConcreteGraphRecovery.integralY)
                (derivative (rhsPoly (R := R₂)))) +
        (2 * N13ConcreteGraphRecovery.integralY +
          aeval
              (algebraMap R₂ IntegralRing E.a +
                algebraMap R₂ IntegralRing E.c *
                  N13ConcreteGraphRecovery.integralY)
              (hPoly (R := R₂))) =
      aeval N13ConcreteGraphRecovery.integralY E.m *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.w) +
        aeval N13ConcreteGraphRecovery.integralY E.w *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.m)
  linear_combination heval

theorem complement_eval_s_eq_derivative
    (E : VerticalGraph) :
    (complementPoly E).eval (sValue E) =
      (derivative curveInX).eval (sValue E) := by
  have hder :=
    divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      curveInX (sValue E)
  have heval := congrArg
    (fun p : IntegralRing[X] => p.eval (sValue E)) hder
  simpa [complementPoly] using heval

theorem exists_jacobianY_decomposition
    (E : VerticalGraph) :
    ∃ β : IntegralRing,
      N13IntegralGraphJacobian.jacobianY =
        U E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.w) +
          G E * β +
          H E * (-algebraMap R₂ IntegralRing E.c) +
          W E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.m) := by
  obtain ⟨qFy, hqFy⟩ :=
    sub_dvd_eval_sub
      N13CanonicalContractionQuotient.integralX
      (sValue E) fyPoly
  obtain ⟨qH, hqH⟩ :=
    sub_dvd_eval_sub
      N13CanonicalContractionQuotient.integralX
      (sValue E) (complementPoly E)
  have hqFy' :
      N13IntegralGraphJacobian.jacobianY -
          fyPoly.eval (sValue E) =
        G E * qFy := by
    simpa [G, fyPoly_eval_integralX] using hqFy
  have hqH' :
      H E - (complementPoly E).eval (sValue E) =
        G E * qH := by
    simpa [G, H] using hqH
  have hHs :=
    complement_eval_s_eq_derivative E
  have htotal :=
    totalDerivative_at_s E
  refine
    ⟨qFy + algebraMap R₂ IntegralRing E.c * qH, ?_⟩
  linear_combination
    hqFy' + htotal +
      algebraMap R₂ IntegralRing E.c * hHs +
      algebraMap R₂ IntegralRing E.c * hqH'

theorem verticalIdeal_isUnit
    (E : VerticalGraph) :
    IsUnit
      ((E.ideal : Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨β, hFy⟩ :=
    exists_jacobianY_decomposition E
  obtain ⟨a, b, hBez⟩ :=
    N13IntegralGraphJacobian.exists_jacobian_bezout
  have hGne : G E ≠ 0 := by
    intro hzero
    have hcoeff :=
      congrArg
        (N13GeneralizedMumfordIntegral.coeff0 (R := R₂))
        hzero
    simp only [G, sValue, VerticalGraph.s, map_add, map_mul,
      Polynomial.aeval_C, aeval_X] at hcoeff
    rw [algebraMap_eq_xClass_C E.a,
      algebraMap_eq_xClass_C E.c] at hcoeff
    simp only [map_sub, map_zero] at hcoeff
    have hcoeffOne :=
      congrArg (fun p : R₂[X] => p.coeff 1) hcoeff
    simpa [G, sValue, VerticalGraph.s,
      N13CanonicalContractionQuotient.integralX,
      N13ConcreteGraphRecovery.integralY] using hcoeffOne
  have hrelation :
      U E * W E = -(G E * H E) := by
    have h := G_mul_H E
    linear_combination h
  have hFx :
      N13IntegralGraphJacobian.jacobianX =
        G E * Hx E + U E * 0 + W E * 0 + H E * 1 := by
    have h := jacobianX_decomposition E
    linear_combination h
  have hFy' :
      N13IntegralGraphJacobian.jacobianY =
        G E * β +
          U E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.w) +
          W E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.m) +
          H E * (-algebraMap R₂ IntegralRing E.c) := by
    have h := hFy
    linear_combination h
  have hunit :=
    GraphJacobianDecompositionFrame.graphJacobian_isUnit_of_decompositions
      (K := FunctionField)
      (U := G E) (G := U E) (H := W E) (W := H E)
      (Fx := N13IntegralGraphJacobian.jacobianX)
      (Fy := N13IntegralGraphJacobian.jacobianY)
      (αx := Hx E) (βx := 0) (γx := 0) (δx := 1)
      (αy := β)
      (βy :=
        aeval N13ConcreteGraphRecovery.integralY
          (derivative E.w))
      (γy :=
        aeval N13ConcreteGraphRecovery.integralY
          (derivative E.m))
      (δy := -algebraMap R₂ IntegralRing E.c)
      (a := a) (b := b)
      hGne hrelation hFx hFy' hBez
  have hideal :
      E.ideal = Ideal.span ({G E, U E} : Set IntegralRing) := by
    apply congrArg Ideal.span
    ext z
    simp [U, G, sValue, or_comm]
  rw [hideal]
  exact hunit

end

end MazurProof.N13VerticalGraphJacobian


