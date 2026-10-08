-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumford_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumford_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:46.73504+00:00
-- url     : https://prove2.me/theorems/8326aa68-a18f-4948-ac29-a7155e32acb6
-- title:
--   FLT.Assumptions.MazurProof.SexticMumford source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumford

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumford
Original leading source comments and nonproject imports are retained below. -/
import Mathlib

set_option autoImplicit false




/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

/-- A smooth monic degree-six hyperelliptic equation. -/
structure Model (K : Type u) [Field K] where
  f : K[X]
  monic : f.Monic
  natDegree : f.natDegree = 6
  separable : f.Separable
  two_ne_zero : (2 : K) ≠ 0

variable {K : Type u} [Field K]

namespace Model

theorem squarefree (M : Model K) : Squarefree M.f :=
  M.separable.squarefree

theorem ne_zero (M : Model K) : M.f ≠ 0 :=
  M.monic.ne_zero

theorem not_isUnit (M : Model K) : ¬IsUnit M.f :=
  Polynomial.not_isUnit_of_natDegree_pos M.f (by rw [M.natDegree]; norm_num)

end Model

variable (M : Model K)

/-! ## The affine coordinate ring -/

/-- The outer variable is `Y`; its coefficients are polynomials in `X`. -/
def curvePoly : K[X][X] :=
  X ^ 2 - C M.f

theorem curvePoly_monic : (curvePoly M).Monic := by
  unfold curvePoly
  monicity!

theorem curvePoly_natDegree : (curvePoly M).natDegree = 2 := by
  unfold curvePoly
  compute_degree!

private theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot (curvePoly M) q := by
  intro hq
  have hsq : q ^ 2 = M.f := by
    simpa only [IsRoot.def, curvePoly, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hq
  have hqunit : IsUnit q := by
    apply M.squarefree q
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hqunit.pow 2
  exact M.not_isUnit hfunit

theorem curvePoly_irreducible : Irreducible (curvePoly M) := by
  rw [(curvePoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot M q
      ((mem_roots (curvePoly_monic M).ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible (curvePoly M)) :=
  ⟨curvePoly_irreducible M⟩

abbrev CoordinateRing : Type u :=
  AdjoinRoot (curvePoly M)

abbrev FunctionField : Type u :=
  FractionRing (CoordinateRing M)

instance instIsDomainCoordinateRing : IsDomain (CoordinateRing M) :=
  AdjoinRoot.isDomain_of_prime (curvePoly_irreducible M).prime

noncomputable instance instAlgebraCoordinateRing : Algebra K (CoordinateRing M) :=
  inferInstance

noncomputable instance instAlgebraPolynomialCoordinateRing : Algebra K[X] (CoordinateRing M) :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing M :=
  AdjoinRoot.mk (curvePoly M)

/-- Embed a polynomial in the `X` coordinate into the coordinate ring. -/
def xClass (p : K[X]) : CoordinateRing M :=
  mk M (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing M :=
  mk M X

@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass M p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (curvePoly_monic M)
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Balanced triples -/

/-- A balanced Mumford representative for a divisor class on a monic sextic
with two distinguished points at infinity. -/
structure Mumford where
  u : K[X]
  v : K[X]
  nInf : ℕ
  u_monic : u.Monic
  deg_u : u.natDegree ≤ 2
  v_reduced : v % u = v
  curve_dvd : u ∣ M.f - v ^ 2
  infinity_bound : u.natDegree + nInf ≤ 2

/-- The unreduced integral version used during ideal multiplication. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  nInf : ℤ
  u_monic : u.Monic
  v_reduced : v % u = v
  curve_dvd : u ∣ M.f - v ^ 2

/-- Forget the balancing bounds while retaining the ideal data. -/
def Mumford.toSemi (D : Mumford M) : SemiMumford M where
  u := D.u
  v := D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := D.v_reduced
  curve_dvd := D.curve_dvd

@[simp] theorem toSemi_u (D : Mumford M) : D.toSemi.u = D.u := rfl

@[simp] theorem toSemi_v (D : Mumford M) : D.toSemi.v = D.v := rfl

@[simp] theorem toSemi_nInf (D : Mumford M) : D.toSemi.nInf = D.nInf := rfl

/-- The balanced representative of the identity class. -/
def zero : Mumford M where
  u := 1
  v := 0
  nInf := 1
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

@[simp] theorem zero_u : (zero M).u = 1 := rfl

@[simp] theorem zero_v : (zero M).v = 0 := rfl

@[simp] theorem zero_nInf : (zero M).nInf = 1 := rfl

/-! ## Curve points and their balanced representatives -/

/-- The two-infinity projective completion of the affine sextic. -/
inductive CurvePoint where
  | infinityPlus
  | infinityMinus
  | affine (x y : K) (onCurve : y ^ 2 = M.f.eval x)

/-- With `∞₊` as base point, an affine point `(x,y)` is represented by
`(X-x,y,0)`. -/
def affinePointMumford (x y : K) (h : y ^ 2 = M.f.eval x) :
    Mumford M where
  u := X - C x
  v := C y
  nInf := 0
  u_monic := monic_X_sub_C x
  deg_u := by simp
  v_reduced := by
    rw [mod_eq_self_iff (monic_X_sub_C x).ne_zero]
    exact degree_C_le.trans_lt (by rw [degree_X_sub_C]; norm_num)
  curve_dvd := by
    have heval : (M.f - (C y) ^ 2).eval x = 0 := by
      rw [eval_sub, eval_pow, eval_C, ← h, sub_self]
    have hd := X_sub_C_dvd_sub_C_eval (p := M.f - (C y) ^ 2) (a := x)
    simpa only [heval, C_0, sub_zero] using hd
  infinity_bound := by simp

/-- The negative point at infinity is represented by `(1,0,0)`. -/
def infinityMinusMumford : Mumford M where
  u := 1
  v := 0
  nInf := 0
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

/-- The balanced representative attached to a projective curve point. -/
def pointMumford : CurvePoint M → Mumford M
  | .infinityPlus => zero M
  | .infinityMinus => infinityMinusMumford M
  | .affine x y h => affinePointMumford M x y h

theorem X_sub_C_ne_one (x : K) :
    (X - C x : K[X]) ≠ 1 := by
  intro h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 1) h
  rw [coeff_one] at hc
  norm_num at hc

theorem X_sub_C_injective :
    Function.Injective (fun x : K ↦ (X - C x : K[X])) := by
  intro x y h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 0) h
  simpa using congrArg Neg.neg hc

/-- Distinct projective points have distinct balanced representatives. -/
theorem pointMumford_injective :
    Function.Injective (pointMumford M) := by
  intro P Q hPQ
  cases P with
  | infinityPlus =>
      cases Q with
      | infinityPlus => rfl
      | infinityMinus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | affine x y h =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
  | infinityMinus =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | infinityMinus => rfl
      | affine x y h =>
          have hu := congrArg Mumford.u hPQ
          change (1 : K[X]) = X - C x at hu
          exact False.elim (X_sub_C_ne_one x hu.symm)
  | affine x y h =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
      | infinityMinus =>
          have hu := congrArg Mumford.u hPQ
          change X - C x = (1 : K[X]) at hu
          exact False.elim (X_sub_C_ne_one x hu)
      | affine x' y' h' =>
          have hu := congrArg Mumford.u hPQ
          have hv := congrArg Mumford.v hPQ
          change X - C x = X - C x' at hu
          change C y = C y' at hv
          have hx : x = x' := X_sub_C_injective hu
          have hy : y = y' := C_injective hv
          subst x'
          subst y'
          rfl

/-! ## Mumford ideals -/

def ySubClass (v : K[X]) : CoordinateRing M :=
  yClass M - xClass M v

def mumfordIdeal (u v : K[X]) : Ideal (CoordinateRing M) :=
  Ideal.span {xClass M u, ySubClass M v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass M u ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_ne_bot (D : Mumford M) :
    mumfordIdeal M D.u D.v ≠ ⊥ := by
  intro hbot
  have hx : xClass M D.u = 0 := by
    have hm := xClass_mem_mumfordIdeal M D.u D.v
    rw [hbot, Ideal.mem_bot] at hm
    exact hm
  exact xClass_ne_zero M D.u_monic.ne_zero hx

/-! ## The oriented fractional-ideal quotient -/

abbrev InvFrac : Type u :=
  (FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))ˣ

abbrev OrientedFrac : Type u :=
  InvFrac M × Multiplicative ℤ

set_option maxHeartbeats 1000000 in
/-- The valuation datum at the chosen positive point at infinity. -/
structure InfinityOrder where
  ordPlus : (FunctionField M)ˣ →* Multiplicative ℤ

def principalOriented (O : InfinityOrder M) :
    (FunctionField M)ˣ →* OrientedFrac M :=
  (toPrincipalIdeal (CoordinateRing M) (FunctionField M)).prod O.ordPlus

abbrev OrientedPic (O : InfinityOrder M) : Type u :=
  Additive (OrientedFrac M ⧸ (principalOriented M O).range)

instance instAddCommGroupOrientedPic (O : InfinityOrder M) : AddCommGroup (OrientedPic M O) :=
  inferInstance

def orientedMk (O : InfinityOrder M) :
    Additive (OrientedFrac M) →+ OrientedPic M O :=
  MonoidHom.toAdditive (QuotientGroup.mk' (principalOriented M O).range)

end

end MazurProof.SexticMumford


