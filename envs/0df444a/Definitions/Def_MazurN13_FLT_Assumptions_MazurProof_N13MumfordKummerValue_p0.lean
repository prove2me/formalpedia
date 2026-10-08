-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerValue_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerValue_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:11:35.141693+00:00
-- url     : https://prove2.me/theorems/e7a7abde-6be9-43d1-917a-205928e10543
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerValue source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerValue

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerValue
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0

set_option autoImplicit false




/-!
# The N13 Mumford fake-Kummer value

Let `θ` be the sextic root.  The branch specialization

`ℚ[X,Y]/(Y²-f(X)) → ℚ(θ),  X ↦ θ,  Y ↦ 0`

turns the quadratic norm of an affine function into a square.  For a
balanced Mumford representative `(u,v,n∞)`, its raw fake-Kummer value is
the unit `u(θ)`, modulo squares and rational scalars.

Irreducibility of the sextic is used only to install the field structure
locally and hence turn the nonzero element `u(θ)` into a unit.  This file
does not yet assert that the value is independent of the chosen Mumford
representative; that is the next principal-ideal relation theorem.
-/

open Polynomial

namespace MazurProof.N13MumfordKummerValue

noncomputable section

open SexticMumford

abbrev f : ℚ[X] :=
  N13SexticSquareclass.f

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField

private theorem thetaBranch_root :
    (curvePoly M).eval₂ (AdjoinRoot.mk f) (0 : L) = 0 := by
  simp only [curvePoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    OfNat.ofNat]
  rw [show M.f = f by rfl, AdjoinRoot.mk_self]
  change (0 : L) ^ 2 - 0 = 0
  norm_num

/-- Specialization to the branch `X=θ`, `Y=0`. -/
def thetaBranch : N13Mumford.CoordinateRing ℚ →+* L :=
  AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root

@[simp] theorem thetaBranch_xClass (p : ℚ[X]) :
    thetaBranch (xClass M p) = AdjoinRoot.mk f p := by
  change
    AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root
        (AdjoinRoot.of (curvePoly M) p) =
      AdjoinRoot.mk f p
  rw [AdjoinRoot.lift_of]

@[simp] theorem thetaBranch_yClass :
    thetaBranch (yClass M) = 0 := by
  exact AdjoinRoot.lift_root thetaBranch_root

theorem thetaBranch_eq_mk_coeff0
    (z : N13Mumford.CoordinateRing ℚ) :
    thetaBranch z = AdjoinRoot.mk f (coeff0 M z) := by
  conv_lhs =>
    rw [← recompose M z]
  simp

theorem thetaBranch_conjugate
    (z : N13Mumford.CoordinateRing ℚ) :
    thetaBranch (conjugate M z) = thetaBranch z := by
  conv_lhs =>
    rw [← recompose M z]
  conv_rhs =>
    rw [← recompose M z]
  simp

/-- At the ramification branch `Y=0`, the hyperelliptic norm is a square. -/
theorem thetaBranch_norm_sq
    (z : N13Mumford.CoordinateRing ℚ) :
    thetaBranch (SexticMumford.norm M z) = thetaBranch z ^ 2 := by
  rw [SexticMumford.norm, map_mul, thetaBranch_conjugate, pow_two]

/-- Evaluation `u(θ)` for a balanced Mumford representative. -/
def uTheta (D : N13Mumford.Mumford ℚ) : L :=
  thetaBranch (xClass M D.u)

@[simp] theorem uTheta_eq_mk (D : N13Mumford.Mumford ℚ) :
    uTheta D = AdjoinRoot.mk f D.u := by
  simp [uTheta]

theorem uTheta_ne_zero (D : N13Mumford.Mumford ℚ) :
    uTheta D ≠ 0 := by
  rw [uTheta_eq_mk]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (N13Mumford.f_monic ℚ) D.u_monic.ne_zero
  change D.u.natDegree < (N13Mumford.f ℚ).natDegree
  rw [N13Mumford.f_natDegree]
  have hdeg : D.u.natDegree ≤ 2 := D.deg_u
  omega

/-- The nonzero field element `u(θ)`, packaged as a unit. -/
def uThetaUnit (D : N13Mumford.Mumford ℚ) : Lˣ :=
  Units.mk0 (uTheta D) (uTheta_ne_zero D)

@[simp] theorem uThetaUnit_val (D : N13Mumford.Mumford ℚ) :
    (uThetaUnit D : L) = uTheta D := rfl

abbrev FakeTarget : Type :=
  Additive (FakeSquareClass.Target (algebraMap ℚ L))

/-- The raw fake-Kummer value of a balanced Mumford representative. -/
def mumfordFakeClass (D : N13Mumford.Mumford ℚ) : FakeTarget :=
  Additive.ofMul
    (((uThetaUnit D : Lˣ)) :
      FakeSquareClass.Target (algebraMap ℚ L))

@[simp] theorem uTheta_zero :
    uTheta (SexticMumford.zero M) = 1 := by
  simp [uTheta]

@[simp] theorem uThetaUnit_zero :
    uThetaUnit (SexticMumford.zero M) = 1 := by
  apply Units.ext
  exact uTheta_zero

@[simp] theorem mumfordFakeClass_zero :
    mumfordFakeClass (SexticMumford.zero M) = 0 := by
  change
    Additive.ofMul
        (((uThetaUnit (SexticMumford.zero M) : Lˣ)) :
          FakeSquareClass.Target (algebraMap ℚ L)) =
      0
  rw [uThetaUnit_zero]
  rfl

/-- A product that differs from a rational scalar by a square gives equal
raw fake-Kummer values.  Principal-ideal geometry will provide precisely
this equality for two representatives of the same class. -/
theorem mumfordFakeClass_eq_of_product_mul_square_eq_scalar
    (D E : N13Mumford.Mumford ℚ)
    (s : Lˣ) (q : ℚˣ)
    (h :
      (uThetaUnit D * uThetaUnit E) * s ^ 2 =
        FakeSquareClass.scalarUnitsMap (algebraMap ℚ L) q) :
    mumfordFakeClass D = mumfordFakeClass E := by
  change
    (((uThetaUnit D : Lˣ)) :
        FakeSquareClass.Target (algebraMap ℚ L)) =
      (((uThetaUnit E : Lˣ)) :
        FakeSquareClass.Target (algebraMap ℚ L))
  rw [FakeSquareClass.target_eq_iff_mul_eq_one]
  exact FakeSquareClass.eq_one_of_mul_sq_eq_scalar
    (algebraMap ℚ L) (uThetaUnit D * uThetaUnit E) s q h

/-- The fake target has exponent two, so every raw value kills doubles. -/
theorem two_nsmul_mumfordFakeClass
    (D : N13Mumford.Mumford ℚ) :
    2 • mumfordFakeClass D = 0 := by
  change
    Additive.ofMul
        (((((uThetaUnit D : Lˣ)) :
          FakeSquareClass.Target (algebraMap ℚ L))) ^ 2) =
      Additive.ofMul 1
  simp

end

end MazurProof.N13MumfordKummerValue


