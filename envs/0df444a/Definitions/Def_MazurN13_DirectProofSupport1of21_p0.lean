-- Prove2me | Definitions.Def_MazurN13_DirectProofSupport1of21_p0
-- name    : MazurN13_DirectProofSupport1of21_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T13:10:52.5019+00:00
-- url     : https://prove2.me/theorems/8d97fbd3-5238-45a1-ab37-7939b644775a
-- title:
--   Order-thirteen exclusion proof support, part 1 of 21
-- statement:
--   Verified auxiliary constructions and lemmas used in the formal proof excluding rational points of order thirteen on elliptic curves over the rationals. This part retains source declarations in dependency order.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580 (N13 formalization; source reconstruction and two elaboration repairs retained locally)

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_PowerBasisDiscriminant_p0
import Definitions.Def_MazurN13_FLT_DedekindDomain_AdicValuation_p0


section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumford
Original leading source comments and nonproject imports are retained below. -/

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


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordBasis
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

def xClassHom : K[X] →+* CoordinateRing M :=
  AdjoinRoot.of (curvePoly M)

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom M p = xClass M p := rfl

@[simp] theorem xClass_zero : xClass M 0 = 0 := by
  exact map_zero (xClassHom M)

@[simp] theorem xClass_one : xClass M 1 = 1 := by
  exact map_one (xClassHom M)

@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass M (p - q) = xClass M p - xClass M q := by
  exact map_sub (xClassHom M) p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass M (-p) = -xClass M p := by
  exact map_neg (xClassHom M) p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass M (p * q) = xClass M p * xClass M q := by
  exact map_mul (xClassHom M) p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass M (p ^ n) = xClass M p ^ n := by
  exact map_pow (xClassHom M) p n

def normalPoly : CoordinateRing M →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic M)

def coeff0 : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp (normalPoly M)

def coeffY : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp (normalPoly M)

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly M (mk M g) = g %ₘ curvePoly M := by
  rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 M (mk M g) = (g %ₘ curvePoly M).coeff 0 := by
  rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY M (mk M g) = (g %ₘ curvePoly M).coeff 1 := by
  rfl

private theorem degree_curvePoly : (curvePoly M).degree = 2 := by
  rw [degree_eq_natDegree (curvePoly_monic M).ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing M) :
    normalPoly M z = C (coeff0 M z) + C (coeffY M z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly M =
        C ((g %ₘ curvePoly M).coeff 0) +
          C ((g %ₘ curvePoly M).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly M) (curvePoly_monic M)
        (n := 2) (by rw [degree_curvePoly]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose (z : CoordinateRing M) :
    xClass M (coeff0 M z) + xClass M (coeffY M z) * yClass M = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass M (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
              xClass M (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * yClass M =
            AdjoinRoot.mk (curvePoly M)
              (C (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
                C (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk (curvePoly M)
              (normalPoly M (AdjoinRoot.mk (curvePoly M) g)) := by
                rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk (curvePoly M) g :=
          AdjoinRoot.mk_leftInverse (curvePoly_monic M)
            (AdjoinRoot.mk (curvePoly M) g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 M (xClass M p) = p := by
  change (C p %ₘ curvePoly M).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY M (xClass M p) = 0 := by
  change (C p %ₘ curvePoly M).coeff 1 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeff0_yClass : coeff0 M (yClass M) = 0 := by
  change (X %ₘ curvePoly M).coeff 0 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

@[simp] theorem coeffY_yClass : coeffY M (yClass M) = 1 := by
  change (X %ₘ curvePoly M).coeff 1 = 1
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

theorem eq_iff_coeff (z w : CoordinateRing M) :
    z = w ↔ coeff0 M z = coeff0 M w ∧ coeffY M z = coeffY M w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose M z, ← recompose M w, h0, hY]

/-! ## Hyperelliptic conjugation and the quadratic norm -/

private theorem neg_y_relation :
    (curvePoly M).eval₂ (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (-(yClass M)) ^ 2 - xClass M M.f = 0
  rw [neg_sq, yClass_sq]
  exact sub_self _

def conjugate : CoordinateRing M →+* CoordinateRing M :=
  AdjoinRoot.lift (AdjoinRoot.of (curvePoly M)) (-(yClass M))
    (neg_y_relation M)

@[simp] theorem conjugate_xClass (p : K[X]) :
    conjugate M (xClass M p) = xClass M p := by
  change conjugate M (AdjoinRoot.of (curvePoly M) p) =
    AdjoinRoot.of (curvePoly M) p
  exact AdjoinRoot.lift_of (neg_y_relation M)

@[simp] theorem conjugate_yClass :
    conjugate M (yClass M) = -(yClass M) := by
  exact AdjoinRoot.lift_root (neg_y_relation M)

theorem conjugate_involutive : Function.Involutive (conjugate M) := by
  have hcomp : (conjugate M).comp (conjugate M) =
      RingHom.id (CoordinateRing M) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro k
        change conjugate M (conjugate M (xClass M (C k))) = xClass M (C k)
        rw [conjugate_xClass, conjugate_xClass]
      · change conjugate M (conjugate M (xClass M X)) = xClass M X
        rw [conjugate_xClass, conjugate_xClass]
    · change conjugate M (conjugate M (yClass M)) = yClass M
      rw [conjugate_yClass, map_neg, conjugate_yClass, neg_neg]
  intro z
  exact DFunLike.congr_fun hcomp z

def norm (z : CoordinateRing M) : CoordinateRing M :=
  z * conjugate M z

theorem norm_recompose (p q : K[X]) :
    norm M (xClass M p + xClass M q * yClass M) =
      xClass M (p ^ 2 - q ^ 2 * M.f) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M p + xClass M q * -yClass M) =
        xClass M p ^ 2 - xClass M q ^ 2 * yClass M ^ 2 := by ring
    _ = xClass M p ^ 2 - xClass M q ^ 2 * xClass M M.f := by
      rw [yClass_sq]
    _ = xClass M (p ^ 2 - q ^ 2 * M.f) := by
      change
        AdjoinRoot.of (curvePoly M) p ^ 2 -
            AdjoinRoot.of (curvePoly M) q ^ 2 *
              AdjoinRoot.of (curvePoly M) M.f =
          AdjoinRoot.of (curvePoly M) (p ^ 2 - q ^ 2 * M.f)
      simp only [map_sub, map_mul, map_pow]

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordNormalForm
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# First normalization step for sextic Mumford ideals

Before choosing a two-generator `K[X]`-basis, a fractional ideal may be
cleared of denominators by a single nonzero element of the coordinate ring.
This is the first, representation-independent step in the normal-form
argument.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Every invertible fractional ideal of the sextic coordinate ring becomes
an integral ideal after multiplication by one nonzero principal factor. -/
theorem invFrac_exists_integral_scaling (M : Model K) (I : InvFrac M) :
    ∃ (a : CoordinateRing M) (J : Ideal (CoordinateRing M)), a ≠ 0 ∧
      (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ * J := by
  exact FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordIdeal
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

abbrev MumfordResidue (D : SemiMumford M) : Type u :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

private theorem mumford_root_relation (D : SemiMumford M) :
    (curvePoly M).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 - M.f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := D.curve_dvd
  refine ⟨-w, ?_⟩
  calc
    D.v ^ 2 - M.f = -(M.f - D.v ^ 2) := by ring
    _ = -(D.u * w) := by rw [hw]
    _ = D.u * (-w) := by ring

def mumfordEval (D : SemiMumford M) :
    CoordinateRing M →+* MumfordResidue M D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation M D)

@[simp] theorem mumfordEval_xClass (D : SemiMumford M) (p : K[X]) :
    mumfordEval M D (xClass M p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval M D (AdjoinRoot.of (curvePoly M) p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation M D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford M) :
    mumfordEval M D (yClass M) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation M D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford M) :
    mumfordEval M D (ySubClass M D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford M) :
    mumfordIdeal M D.u D.v ≤ RingHom.ker (mumfordEval M D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval M D (xClass M D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · change mumfordEval M D (ySubClass M D.v) = 0
    rw [mumfordEval_ySubClass]

theorem ker_mumfordEval (D : SemiMumford M) :
    RingHom.ker (mumfordEval M D) = mumfordIdeal M D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 M z
    let q : K[X] := coeffY M z
    have hz' : mumfordEval M D
        (xClass M p + xClass M q * yClass M) = 0 := by
      rw [recompose M z]
      exact hz
    have hquot : Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass, map_add, map_mul] using hz'
    have hdvd : D.u ∣ p + q * D.v := by
      exact Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass M D.u ∈ mumfordIdeal M D.u D.v :=
      xClass_mem_mumfordIdeal M D.u D.v
    have hyv : ySubClass M D.v ∈ mumfordIdeal M D.u D.v :=
      Ideal.subset_span (by simp)
    have hbase : xClass M (p + q * D.v) ∈
        mumfordIdeal M D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M s) hu
    have hgraph : xClass M q * ySubClass M D.v ∈
        mumfordIdeal M D.u D.v :=
      Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M q) hyv
    rw [← recompose M z]
    have hdecomp :
        xClass M p + xClass M q * yClass M =
          xClass M (p + q * D.v) + xClass M q * ySubClass M D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker M D

theorem mumfordEval_surjective (D : SemiMumford M) :
    Function.Surjective (mumfordEval M D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass M p, mumfordEval_xClass M D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford M) :
    CoordinateRing M ⧸ mumfordIdeal M D.u D.v ≃+*
      MumfordResidue M D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval M D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective M D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford M) (z : CoordinateRing M) :
    mumfordQuotientEquiv M D
        (Ideal.Quotient.mk (mumfordIdeal M D.u D.v) z) =
      mumfordEval M D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford M) :
    (CoordinateRing M ⧸ mumfordIdeal M D.u D.v) ≃ₐ[K]
      MumfordResidue M D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv M D)
    (by
      intro r
      change
        mumfordQuotientEquiv M D
            (Ideal.Quotient.mk
              (mumfordIdeal M D.u D.v) (xClass M (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

theorem mumfordIdeal_comap_base (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v).comap (xClassHom M) =
      Ideal.span ({D.u} : Set K[X]) := by
  rw [← ker_mumfordEval]
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, xClassHom_apply,
    mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem]

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordUnit
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Explicit invertibility of Mumford ideals on a smooth sextic

For a semi-Mumford pair `(u,v)`, squarefreeness of the sextic gives
`(u, 2v, (f-v²)/u) = 1`.  Consequently `(u,Y-v) (u,Y+v) = (u)`,
which packages the Mumford ideal as a unit fractional ideal.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem mumford_bezout (D : SemiMumford M) :
    ∃ w a b c : K[X],
      M.f - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : C (2 : K) = (2 : K[X]) := by
          exact map_natCast (C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr M.two_ne_zero)
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ M.f - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ M.f := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        M.ne_zero).mp M.squarefree z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass M v ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_mul_conj_integral (D : SemiMumford M) :
    mumfordIdeal M D.u D.v * mumfordIdeal M D.u (-D.v) =
      Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M D.u D.v
  let J := mumfordIdeal M D.u (-D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨p₀ * q₀ * xClass M D.u +
        p₀ * qY * ySubClass M (-D.v) +
        pY * q₀ * ySubClass M D.v +
        pY * qY * xClass M w, ?_⟩
    rw [← hpEq, ← hqEq]
    simp only [ySubClass, xClass_neg, sub_neg_eq_add] at hpEq hqEq ⊢
    have hgraph :
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
          xClass M D.u * xClass M w := by
      calc
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
            yClass M ^ 2 - xClass M D.v ^ 2 := by ring
        _ = xClass M M.f - xClass M (D.v ^ 2) := by
          rw [yClass_sq, xClass_pow]
        _ = xClass M (M.f - D.v ^ 2) := by rw [xClass_sub]
        _ = xClass M (D.u * w) := by rw [hw]
        _ = xClass M D.u * xClass M w := by rw [xClass_mul]
    linear_combination pY * qY * hgraph
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨w, a, b, c, hw, hbez⟩ := mumford_bezout M D
    have huI : xClass M D.u ∈ I :=
      xClass_mem_mumfordIdeal M D.u D.v
    have huJ : xClass M D.u ∈ J :=
      xClass_mem_mumfordIdeal M D.u (-D.v)
    have hvI : ySubClass M D.v ∈ I :=
      ySubClass_mem_mumfordIdeal M D.u D.v
    have hvJ : ySubClass M (-D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal M D.u (-D.v)
    have hu2 : xClass M D.u * xClass M D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass M D.u * xClass M (2 * D.v) ∈ I * J := by
      have hp : xClass M D.u * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm : ySubClass M D.v * xClass M D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add, xClass_mul]
      change xClass M D.u * (2 * xClass M D.v) =
        xClass M D.u * (yClass M + xClass M D.v) -
          (yClass M - xClass M D.v) * xClass M D.u
      ring
    have huw : xClass M D.u * xClass M w ∈ I * J := by
      have hg : ySubClass M D.v * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      convert hg using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add]
      calc
        xClass M D.u * xClass M w = xClass M (D.u * w) := by
          rw [xClass_mul]
        _ = xClass M (M.f - D.v ^ 2) := by rw [hw]
        _ = xClass M M.f - xClass M (D.v ^ 2) := by rw [xClass_sub]
        _ = yClass M ^ 2 - xClass M D.v ^ 2 := by
          rw [yClass_sq, xClass_pow]
        _ = (yClass M - xClass M D.v) *
            (yClass M + xClass M D.v) := by ring
    have ha : xClass M a * (xClass M D.u * xClass M D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M a) hu2
    have hb : xClass M b *
        (xClass M D.u * xClass M (2 * D.v)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M b) huv
    have hc : xClass M c * (xClass M D.u * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M c) huw
    have hsum := Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M D.u * xClass M D.u) +
            xClass M b * (xClass M D.u * xClass M (2 * D.v)) +
            xClass M c * (xClass M D.u * xClass M w) =
          xClass M D.u := by
      calc
        _ = xClass M D.u *
            xClass M (a * D.u + b * (2 * D.v) + c * w) := by
              simp only [xClass_add, xClass_mul]
              ring
        _ = xClass M D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass M D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

def mumfordIdealUnit (D : SemiMumford M) : InvFrac M :=
  Units.mkOfMulEqOne
    (mumfordIdeal M D.u D.v :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
    ((mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        (FunctionField M) (xClass_ne_zero M D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford M) :
    (mumfordIdealUnit M D :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      mumfordIdeal M D.u D.v := rfl

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticOrientedPic
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# The concrete oriented Picard group of a smooth sextic

The affine coordinate ring omits the two points at infinity.  An
`InfinityOrder` supplies the order at the chosen point before quotienting by
principal fractional ideals.  This file packages balanced Mumford data into
that oriented quotient for an arbitrary smooth monic sextic model.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

/-- The oriented Picard group attached to the affine sextic and the chosen
order at infinity. -/
abbrev ConcretePic : Type u :=
  OrientedPic M O

/-- The oriented invertible fractional ideal represented by balanced Mumford
data. -/
def mumfordRaw (D : Mumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D.toSemi,
    Multiplicative.ofAdd ((D.nInf : ℤ) - 1))

/-- The oriented Picard class of a balanced Mumford representative. -/
def classOf (D : Mumford M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      (mumfordRaw M D)

theorem classOf_eq_iff (D₁ D₂ : Mumford M) :
    classOf M O D₁ = classOf M O D₂ ↔
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁.toSemi *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
            mumfordIdealUnit M D₂.toSemi ∧
        Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * O.ordPlus α =
            Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₁) =
      QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    refine ⟨α, ?_, ?_⟩
    · exact congrArg Prod.fst hmul
    · exact congrArg Prod.snd hmul
  · rintro ⟨α, hIdeal, hInf⟩
    refine ⟨principalOriented M O α,
      MonoidHom.mem_range.mpr ⟨α, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

theorem zero_mumfordIdeal :
    mumfordIdeal M (zero M).u (zero M).v = ⊤ := by
  rw [zero_u, zero_v, mumfordIdeal]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp [xClass_one])

theorem mumfordIdealUnit_zero :
    mumfordIdealUnit M (zero M).toSemi = 1 := by
  apply Units.ext
  change (mumfordIdeal M 1 0 :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl

@[simp] theorem classOf_zero : classOf M O (zero M) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range
        (mumfordRaw M (zero M))) = 0
  have hraw : mumfordRaw M (zero M) = 1 := by
    apply Prod.ext
    · exact mumfordIdealUnit_zero M
    · simp [mumfordRaw]
  rw [hraw, map_one]
  rfl

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordNorm
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem xClass_injective (M : Model K) :
    Function.Injective (xClass M) := by
  intro p q hpq
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  exact xClass_ne_zero M hsub (by
    rw [xClass_sub, hpq, sub_self])

theorem norm_mul (M : Model K) (z w : CoordinateRing M) :
    norm M (z * w) = norm M z * norm M w := by
  simp only [norm, map_mul]
  ring

@[simp] theorem norm_xClass (M : Model K) (p : K[X]) :
    norm M (xClass M p) = xClass M (p ^ 2) := by
  calc
    norm M (xClass M p) = xClass M p * xClass M p := by
      simp only [norm, conjugate_xClass]
    _ = xClass M (p * p) := (xClass_mul M p p).symm
    _ = xClass M (p ^ 2) := by rw [pow_two]

theorem norm_eq_xClass_coeff (M : Model K) (z : CoordinateRing M) :
    norm M z =
      xClass M
        ((coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f) := by
  conv_lhs =>
    rw [← recompose M z]
  exact norm_recompose M (coeff0 M z) (coeffY M z)

@[simp] theorem coeffY_xClass_mul (M : Model K)
    (a : K[X]) (z : CoordinateRing M) :
    coeffY M (xClass M a * z) = a * coeffY M z := by
  rw [show xClass M a =
    algebraMap K[X] (CoordinateRing M) a from rfl]
  rw [← Algebra.smul_def, map_smul]
  rfl

@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]

theorem dvd_of_xClass_mul_ySubClass_mem_span
    (M : Model K) (u a v : K[X])
    (h : xClass M a * ySubClass M v ∈
      Ideal.span ({xClass M u} : Set (CoordinateRing M))) :
    u ∣ a := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨coeffY M t, ?_⟩
  have hc := congrArg (coeffY M) ht
  rw [coeffY_xClass_mul, coeffY_ySubClass, mul_one,
    coeffY_xClass_mul] at hc
  exact hc

theorem u_dvd_of_scaled_mumfordIdeal_eq
    (M : Model K) (u₁ v₁ u₂ v₂ : K[X])
    (h :
      mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) =
        mumfordIdeal M u₂ v₂ *
          Ideal.span ({xClass M u₁} : Set (CoordinateRing M))) :
    u₁ ∣ u₂ := by
  have hyv :
      ySubClass M v₁ ∈ mumfordIdeal M u₁ v₁ :=
    Ideal.subset_span (by simp)
  have hu :
      xClass M u₂ ∈
        Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.subset_span (by simp)
  have hmem :
      ySubClass M v₁ * xClass M u₂ ∈
        mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.mul_mem_mul hyv hu
  rw [h] at hmem
  have hspan :
      xClass M u₂ * ySubClass M v₁ ∈
        Ideal.span ({xClass M u₁} : Set (CoordinateRing M)) := by
    rw [mul_comm]
    exact Ideal.mul_le_right hmem
  exact dvd_of_xClass_mul_ySubClass_mem_span M u₁ u₂ v₁ hspan

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordRepresentative
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

/- Keep generated structure auxiliaries from expanding the coordinate-ring
presentation while comparing fields under independent parameters. These aliases
are reducible again immediately after the structure is generated. -/
private def IntegralRepIdeal : Type u := Ideal (CoordinateRing M)
private def IntegralRepUnit : Type u := InvFrac M
private def IntegralRepCoeEq (I : IntegralRepIdeal M) (z : IntegralRepUnit M) : Prop :=
  ((show InvFrac M from z) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((show Ideal (CoordinateRing M) from I) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

section
attribute [local irreducible] IntegralRepIdeal IntegralRepUnit

/-- An oriented representative whose finite component is an integral ideal.
The unit remembers that this ideal is invertible as a fractional ideal. -/
structure IntegralOrientedRep where
  ideal : IntegralRepIdeal M
  unit : IntegralRepUnit M
  coe_unit : IntegralRepCoeEq M ideal unit
  atInfinity : ℤ

end
attribute [reducible] IntegralRepIdeal IntegralRepUnit IntegralRepCoeEq

namespace IntegralOrientedRep

/-- The raw oriented fractional ideal underlying an integral representative. -/
def raw (R : IntegralOrientedRep M) : OrientedFrac M :=
  (R.unit, Multiplicative.ofAdd R.atInfinity)

/-- The oriented Picard class of an integral representative. -/
def picClass (R : IntegralOrientedRep M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range (R.raw M)

theorem ideal_ne_bot (R : IntegralOrientedRep M) : R.ideal ≠ ⊥ := by
  intro h
  have hzero :
      (R.unit :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 0 := by
    rw [R.coe_unit, h]
    rfl
  exact R.unit.ne_zero hzero

theorem ideal_isUnit (R : IntegralOrientedRep M) :
    IsUnit
      (R.ideal :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  exact ⟨R.unit, R.coe_unit⟩

end IntegralOrientedRep

/-- The affine coordinate ring is free of rank two over `K[X]`, with the
power basis `1,Y`.  The index is rewritten using the proved degree of the
quadratic equation rather than by computation. -/
def polynomialBasis :
    Module.Basis (Fin 2) K[X] (CoordinateRing M) :=
  (AdjoinRoot.powerBasis' (curvePoly_monic M)).basis.reindex
    (finCongr (curvePoly_natDegree M))

/-- Every nonzero integral ideal is a rank-two `K[X]`-lattice.  Mathlib's
PID structure theorem supplies compatible two-element bases for the ambient
coordinate ring and the ideal. -/
theorem ideal_exists_two_generator_smith_form
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    ∃ (bR : Module.Basis (Fin 2) K[X] (CoordinateRing M))
      (a : Fin 2 → K[X])
      (bJ : Module.Basis (Fin 2) K[X] J),
      ∀ i, (bJ i : CoordinateRing M) = a i • bR i := by
  exact Ideal.exists_smith_normal_form (polynomialBasis M) J hJ

/-- In particular, the integral ideal attached to every oriented
representative has a structural two-generator Smith presentation. -/
theorem IntegralOrientedRep.exists_two_generator_smith_form
    (R : IntegralOrientedRep M) :
    ∃ (bR : Module.Basis (Fin 2) K[X] (CoordinateRing M))
      (a : Fin 2 → K[X])
      (bJ : Module.Basis (Fin 2) K[X] R.ideal),
      ∀ i, (bJ i : CoordinateRing M) = a i • bR i := by
  exact ideal_exists_two_generator_smith_form M R.ideal
    (R.ideal_ne_bot M)

/-- Contract an integral ideal from the quadratic coordinate ring to its
polynomial subring. -/
def idealContraction (J : Ideal (CoordinateRing M)) : Ideal K[X] :=
  J.comap (xClassHom M)

/-- A nonzero ideal has nonzero contraction to `K[X]`.  The structural
reason is that the quadratic norm of any nonzero ideal element is a nonzero
polynomial lying in the contraction. -/
theorem idealContraction_ne_bot (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : idealContraction M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let p : K[X] :=
    (coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f
  have hconj : conjugate M z ≠ 0 := by
    intro hc
    apply hz
    calc
      z = conjugate M (conjugate M z) :=
        (conjugate_involutive M z).symm
      _ = 0 := by rw [hc, map_zero]
  have hnorm : norm M z ≠ 0 :=
    mul_ne_zero hz hconj
  have hp : p ≠ 0 := by
    intro hp
    apply hnorm
    rw [norm_eq_xClass_coeff]
    change xClass M p = 0
    rw [hp, xClass_zero]
  intro hbot
  have hpmem : p ∈ idealContraction M J := by
    change xClass M p ∈ J
    rw [← norm_eq_xClass_coeff]
    exact J.mul_mem_right (conjugate M z) hzJ
  rw [hbot, Ideal.mem_bot] at hpmem
  exact hp hpmem

/-- The canonical monic generator of the contraction of an integral ideal
to `K[X]`. -/
def contractionGenerator (J : Ideal (CoordinateRing M)) : K[X] := by
  classical
  exact normalize
    (Submodule.IsPrincipal.generator (idealContraction M J))

theorem contractionGenerator_monic (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : (contractionGenerator M J).Monic := by
  classical
  unfold contractionGenerator
  apply Polynomial.monic_normalize
  intro hgen
  exact idealContraction_ne_bot M J hJ
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (idealContraction M J)).mpr hgen)

theorem span_contractionGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contractionGenerator M J} : Set K[X]) =
      idealContraction M J := by
  classical
  unfold contractionGenerator
  calc
    Ideal.span
        ({normalize
          (Submodule.IsPrincipal.generator
            (idealContraction M J))} : Set K[X]) =
        Ideal.span
          ({Submodule.IsPrincipal.generator
            (idealContraction M J)} : Set K[X]) := by
      apply Ideal.span_singleton_eq_span_singleton.mpr
      exact (associated_normalize
        (Submodule.IsPrincipal.generator
          (idealContraction M J))).symm
    _ = idealContraction M J :=
      Ideal.span_singleton_generator (idealContraction M J)

theorem xClass_contractionGenerator_mem
    (J : Ideal (CoordinateRing M)) :
    xClass M (contractionGenerator M J) ∈ J := by
  change contractionGenerator M J ∈ idealContraction M J
  rw [← span_contractionGenerator M J]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- On an existing balanced Mumford ideal, the canonical contraction
generator recovers its `u`-polynomial. -/
theorem contractionGenerator_mumfordIdeal (D : Mumford M) :
    contractionGenerator M (mumfordIdeal M D.u D.v) = D.u := by
  apply Polynomial.eq_of_monic_of_associated
    (contractionGenerator_monic M _
      (mumfordIdeal_ne_bot M D))
    D.u_monic
  apply Ideal.span_singleton_eq_span_singleton.mp
  calc
    Ideal.span
        ({contractionGenerator M
          (mumfordIdeal M D.u D.v)} : Set K[X]) =
        idealContraction M (mumfordIdeal M D.u D.v) :=
      span_contractionGenerator M _
    _ = Ideal.span ({D.u} : Set K[X]) :=
      mumfordIdeal_comap_base M D.toSemi

/-- If an integral ideal has contraction `(u)` and contains one graph
generator `Y-v`, then it is exactly the corresponding Mumford ideal.  This
is the quadratic Hermite-normal-form step, proved from the rank-two
coefficient decomposition. -/
theorem mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    (J : Ideal (CoordinateRing M)) (u v : K[X])
    (hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]))
    (hgraph : ySubClass M v ∈ J) :
    mumfordIdeal M u v = J := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change u ∈ idealContraction M J
      rw [hcontraction]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact hgraph
  · intro w hw
    let q : K[X] := coeffY M w
    let r : CoordinateRing M :=
      w - xClass M q * ySubClass M v
    have hrJ : r ∈ J :=
      J.sub_mem hw (J.mul_mem_left (xClass M q) hgraph)
    have hrY : coeffY M r = 0 := by
      simp [r, q]
    have hrRecompose : xClass M (coeff0 M r) = r := by
      simpa [hrY] using recompose M r
    have hrContract :
        coeff0 M r ∈ idealContraction M J := by
      change xClass M (coeff0 M r) ∈ J
      rw [hrRecompose]
      exact hrJ
    rw [hcontraction, Ideal.mem_span_singleton] at hrContract
    obtain ⟨t, ht⟩ := hrContract
    have hrMumford : r ∈ mumfordIdeal M u v := by
      rw [← hrRecompose, ht, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left _ (xClass M t)
        (xClass_mem_mumfordIdeal M u v)
    have hgraphMumford :
        xClass M q * ySubClass M v ∈ mumfordIdeal M u v :=
      Ideal.mul_mem_left _ (xClass M q)
        (Ideal.subset_span (by simp))
    have hwdecomp :
        w = r + xClass M q * ySubClass M v := by
      simp [r]
    rw [hwdecomp]
    exact Ideal.add_mem _ hrMumford hgraphMumford

/-- An integral ideal is primitive when some element has `Y`-coefficient
one.  This is the exact algebraic hypothesis needed to put it in Mumford
graph form. -/
def IdealIsPrimitive (J : Ideal (CoordinateRing M)) : Prop :=
  ∃ z ∈ J, coeffY M z = 1

/-- A primitive nonzero integral ideal has a semireduced Mumford
presentation.  The `u`-polynomial is the canonical contraction generator,
and `v` is reduced modulo `u`.  No degree bound or class enumeration enters
the proof. -/
theorem exists_semiMumford_of_primitive
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥)
    (hprimitive : IdealIsPrimitive M J) (n : ℤ) :
    ∃ D : SemiMumford M,
      mumfordIdeal M D.u D.v = J ∧
      D.u = contractionGenerator M J ∧
      D.nInf = n := by
  obtain ⟨z, hzJ, hzY⟩ := hprimitive
  let u : K[X] := contractionGenerator M J
  let v0 : K[X] := -(coeff0 M z)
  let v : K[X] := v0 % u
  have huMonic : u.Monic :=
    contractionGenerator_monic M J hJ
  have hu : u ≠ 0 := huMonic.ne_zero
  have hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]) :=
    (span_contractionGenerator M J).symm
  have hgraph0 : ySubClass M v0 = z := by
    calc
      ySubClass M v0 =
          xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              simp [ySubClass, v0, hzY]
              ring
      _ = z := recompose M z
  have hvdecomp : v + u * (v0 / u) = v0 :=
    EuclideanDomain.mod_add_div v0 u
  have hgraph : ySubClass M v ∈ J := by
    have hpoly : v0 - v = u * (v0 / u) := by
      calc
        v0 - v = (v + u * (v0 / u)) - v :=
          congrArg (fun t : K[X] => t - v) hvdecomp.symm
        _ = u * (v0 / u) := by ring
    have hmultiple :
        xClass M (v0 - v) ∈ J := by
      rw [hpoly, xClass_mul, mul_comm]
      exact J.mul_mem_left (xClass M (v0 / u))
        (xClass_contractionGenerator_mem M J)
    have heq :
        ySubClass M v =
          ySubClass M v0 + xClass M (v0 - v) := by
      simp [ySubClass, xClass_sub]
    rw [heq]
    exact J.add_mem (hgraph0 ▸ hzJ) hmultiple
  have hcurve : u ∣ M.f - v ^ 2 := by
    have hprod :
        ySubClass M v * (yClass M + xClass M v) =
          xClass M (M.f - v ^ 2) := by
      simp only [ySubClass]
      calc
        (yClass M - xClass M v) *
            (yClass M + xClass M v) =
            yClass M ^ 2 - xClass M v ^ 2 := by ring
        _ = xClass M M.f - xClass M v ^ 2 := by
          rw [yClass_sq]
        _ = xClass M (M.f - v ^ 2) := by
          rw [xClass_sub, xClass_pow]
    have hmem :
        M.f - v ^ 2 ∈ idealContraction M J := by
      change xClass M (M.f - v ^ 2) ∈ J
      rw [← hprod]
      exact J.mul_mem_right (yClass M + xClass M v) hgraph
    rw [hcontraction, Ideal.mem_span_singleton] at hmem
    exact hmem
  let D : SemiMumford M :=
    { u := u
      v := v
      nInf := n
      u_monic := huMonic
      v_reduced := by
        rw [Polynomial.mod_eq_self_iff hu]
        exact EuclideanDomain.mod_lt _ hu
      curve_dvd := hcurve }
  refine ⟨D, ?_, rfl, rfl⟩
  exact mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    M J u v hcontraction hgraph

/-- Every raw oriented fractional ideal is equivalent, modulo a principal
oriented ideal, to one with an integral finite component. -/
theorem exists_integralRep_of_raw (I : InvFrac M)
    (n : Multiplicative ℤ) :
    ∃ R : IntegralOrientedRep M,
      QuotientGroup.mk' (principalOriented M O).range (I, n) =
        Additive.toMul (R.picClass M O) := by
  obtain ⟨a, J, ha, hI⟩ := invFrac_exists_integral_scaling M I
  have haMap :
      algebraMap (CoordinateRing M) (FunctionField M) a ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (show a ∈ (CoordinateRing M)⁰ from
        mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  let alpha : (FunctionField M)ˣ :=
    Units.mk0
      (algebraMap (CoordinateRing M) (FunctionField M) a) haMap
  let U : InvFrac M :=
    I * toPrincipalIdeal (CoordinateRing M) (FunctionField M) alpha
  have hU :
      (U :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = J := by
    simp only [U, Units.val_mul, coe_toPrincipalIdeal, alpha,
      Units.val_mk0]
    rw [hI]
    calc
      (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) *
          FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a) =
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
            FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)) *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
              ac_rfl
      _ = J := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        simp [haMap]
  let R : IntegralOrientedRep M :=
    { ideal := J
      unit := U
      coe_unit := hU
      atInfinity :=
        Multiplicative.toAdd (n * O.ordPlus alpha) }
  refine ⟨R, ?_⟩
  change
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
      QuotientGroup.mk' (principalOriented M O).range
        (U, Multiplicative.ofAdd R.atInfinity)
  have hprincipal :
      QuotientGroup.mk' (principalOriented M O).range
          (principalOriented M O alpha) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff
      (principalOriented M O alpha)).2
      (MonoidHom.mem_range.mpr ⟨alpha, rfl⟩)
  calc
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
        QuotientGroup.mk' (principalOriented M O).range
          ((I, n) * principalOriented M O alpha) := by
            rw [map_mul, hprincipal]
            exact (mul_one (QuotientGroup.mk'
              (principalOriented M O).range (I, n))).symm
    _ = QuotientGroup.mk' (principalOriented M O).range
          (U, Multiplicative.ofAdd R.atInfinity) := by
            rfl

/-- Every oriented Picard class has an integral invertible-ideal
representative.  No Dedekind-domain or class-number hypothesis is used. -/
theorem exists_integralRepresentative (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M, R.picClass M O = c := by
  change
    ∃ R : IntegralOrientedRep M,
      Additive.toMul (R.picClass M O) = Additive.toMul c
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (principalOriented M O).range
      (Additive.toMul c)
  obtain ⟨R, hR⟩ :=
    exists_integralRep_of_raw M O x.1 x.2
  exact ⟨R, hR.symm.trans hx⟩

/-- Integral ideal reduction is the only extra input needed for existence of
balanced Mumford representatives. -/
theorem classOf_surjective_of_integral_reduction
    (reduce :
      ∀ R : IntegralOrientedRep M,
        ∃ D : Mumford M, classOf M O D = R.picClass M O) :
    Function.Surjective (classOf M O) := by
  intro c
  obtain ⟨R, hR⟩ := exists_integralRepresentative M O c
  obtain ⟨D, hD⟩ := reduce R
  exact ⟨D, hD.trans hR⟩

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Primitive content of an integral sextic ideal

Every integral ideal in the quadratic coordinate ring has a polynomial
content: the common principal ideal generated by all of its `Y`
coefficients.  Dividing by that content is implemented as a colon ideal.
This gives a primitive integral ideal structurally, without enumeration or
Riemann--Roch.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

/-! ## The coefficient-content ideal -/

/-- The ideal of all `Y` coefficients of elements of an integral ideal. -/
def yCoeffIdeal (J : Ideal (CoordinateRing M)) : Ideal K[X] where
  carrier :=
    { b | ∃ z : CoordinateRing M, z ∈ J ∧ coeffY M z = b }
  zero_mem' := ⟨0, J.zero_mem, map_zero (coeffY M)⟩
  add_mem' := by
    rintro b₁ b₂ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₁ + z₂, J.add_mem hz₁ hz₂, map_add (coeffY M) z₁ z₂⟩
  smul_mem' := by
    rintro r b ⟨z, hz, rfl⟩
    refine ⟨xClass M r * z, J.mul_mem_left (xClass M r) hz, ?_⟩
    exact coeffY_xClass_mul M r z

@[simp] theorem mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) (b : K[X]) :
    b ∈ yCoeffIdeal M J ↔
      ∃ z : CoordinateRing M, z ∈ J ∧ coeffY M z = b :=
  Iff.rfl

theorem coeffY_mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    coeffY M z ∈ yCoeffIdeal M J :=
  ⟨z, hz, rfl⟩

/-- Multiplication by `Y` exchanges the two coefficients, up to the
quadratic equation in the constant coefficient. -/
@[simp] theorem coeffY_yClass_mul (z : CoordinateRing M) :
    coeffY M (yClass M * z) = coeff0 M z := by
  conv_lhs =>
    rw [← recompose M z]
  rw [mul_add, map_add]
  have hfirst :
      coeffY M (yClass M * xClass M (coeff0 M z)) =
        coeff0 M z := by
    rw [mul_comm, coeffY_xClass_mul, coeffY_yClass, mul_one]
  have hsecond :
      coeffY M
          (yClass M *
            (xClass M (coeffY M z) * yClass M)) = 0 := by
    calc
      coeffY M
          (yClass M *
            (xClass M (coeffY M z) * yClass M)) =
          coeffY M
            (xClass M (coeffY M z) * yClass M ^ 2) := by
              congr 1
              ring
      _ = coeffY M
            (xClass M (coeffY M z) * xClass M M.f) := by
              rw [yClass_sq]
      _ = coeffY M (xClass M (coeffY M z * M.f)) := by
              rw [xClass_mul]
      _ = 0 := coeffY_xClass M _
  rw [hfirst, hsecond, add_zero]

/-- Ideal stability under multiplication by `Y` puts the constant
coefficient in the same content ideal. -/
theorem coeff0_mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    coeff0 M z ∈ yCoeffIdeal M J := by
  refine ⟨yClass M * z, J.mul_mem_left (yClass M) hz, ?_⟩
  exact coeffY_yClass_mul M z

theorem yCoeffIdeal_ne_bot
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    yCoeffIdeal M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  intro hbot
  have hY : coeffY M z = 0 := by
    rw [← Ideal.mem_bot, ← hbot]
    exact coeffY_mem_yCoeffIdeal M J hzJ
  have h0 : coeff0 M z = 0 := by
    rw [← Ideal.mem_bot, ← hbot]
    exact coeff0_mem_yCoeffIdeal M J hzJ
  apply hz
  rw [← recompose M z, h0, hY, xClass_zero, zero_mul, add_zero]

/-- A canonical (not prematurely normalized) generator of the coefficient
content. -/
def contentGenerator (J : Ideal (CoordinateRing M)) : K[X] :=
  Submodule.IsPrincipal.generator (yCoeffIdeal M J)

theorem span_contentGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contentGenerator M J} : Set K[X]) =
      yCoeffIdeal M J :=
  Ideal.span_singleton_generator (yCoeffIdeal M J)

theorem contentGenerator_ne_zero
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    contentGenerator M J ≠ 0 := by
  intro hzero
  apply yCoeffIdeal_ne_bot M J hJ
  exact
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (yCoeffIdeal M J)).2 hzero

/-- Every element of `J` is visibly divisible in the coordinate ring by
the coefficient-content generator. -/
theorem exists_content_factor
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    ∃ q : CoordinateRing M,
      xClass M (contentGenerator M J) * q = z := by
  have h0 := coeff0_mem_yCoeffIdeal M J hz
  have hY := coeffY_mem_yCoeffIdeal M J hz
  rw [← span_contentGenerator M J, Ideal.mem_span_singleton] at h0 hY
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := hY
  refine ⟨xClass M a + xClass M b * yClass M, ?_⟩
  calc
    xClass M (contentGenerator M J) *
          (xClass M a + xClass M b * yClass M) =
        xClass M (contentGenerator M J * a) +
          xClass M (contentGenerator M J * b) * yClass M := by
            simp only [mul_add, xClass_mul]
            ring
    _ = xClass M (coeff0 M z) +
          xClass M (coeffY M z) * yClass M := by
            rw [← ha, ← hb]
    _ = z := recompose M z

/-! ## Division by content as a colon ideal -/

/-- The integral colon ideal `{z | d z ∈ J}`. -/
def primitivePart
    (J : Ideal (CoordinateRing M)) (d : K[X]) :
    Ideal (CoordinateRing M) where
  carrier := {z | xClass M d * z ∈ J}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    simpa [mul_add] using J.add_mem hz hw
  smul_mem' := by
    intro a z hz
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left a hz

@[simp] theorem mem_primitivePart
    (J : Ideal (CoordinateRing M)) (d : K[X])
    (z : CoordinateRing M) :
    z ∈ primitivePart M J d ↔ xClass M d * z ∈ J :=
  Iff.rfl

/-- Exact content factorization of the original integral ideal. -/
theorem span_content_mul_primitivePart
    (J : Ideal (CoordinateRing M)) :
    Ideal.span
          ({xClass M (contentGenerator M J)} :
            Set (CoordinateRing M)) *
        primitivePart M J (contentGenerator M J) =
      J := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr z hz
    rw [Ideal.mem_span_singleton'] at hr
    obtain ⟨a, rfl⟩ := hr
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left a hz
  · rw [Ideal.le_span_singleton_mul_iff]
    intro z hz
    obtain ⟨q, hq⟩ := exists_content_factor M J hz
    refine ⟨q, ?_, hq⟩
    change xClass M (contentGenerator M J) * q ∈ J
    rw [hq]
    exact hz

/-- The divided ideal contains an element with `Y` coefficient one. -/
theorem primitivePart_isPrimitive
    (J : Ideal (CoordinateRing M)) :
    IdealIsPrimitive M
      (primitivePart M J (contentGenerator M J)) := by
  have hd :
      contentGenerator M J ∈ yCoeffIdeal M J :=
    Submodule.IsPrincipal.generator_mem (yCoeffIdeal M J)
  obtain ⟨z, hzJ, hzY⟩ := hd
  have h0 := coeff0_mem_yCoeffIdeal M J hzJ
  rw [← span_contentGenerator M J, Ideal.mem_span_singleton] at h0
  obtain ⟨c, hc⟩ := h0
  let q : CoordinateRing M := xClass M c + yClass M
  have hdq :
      xClass M (contentGenerator M J) * q = z := by
    calc
      xClass M (contentGenerator M J) * q =
          xClass M (contentGenerator M J * c) +
            xClass M (contentGenerator M J) * yClass M := by
              simp only [q, mul_add, xClass_mul]
      _ = xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              rw [← hc, hzY]
      _ = z := recompose M z
  refine ⟨q, ?_, ?_⟩
  · change xClass M (contentGenerator M J) * q ∈ J
    rw [hdq]
    exact hzJ
  · simp [q]

theorem yCoeffIdeal_primitivePart_eq_top
    (J : Ideal (CoordinateRing M)) :
    yCoeffIdeal M
      (primitivePart M J (contentGenerator M J)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  obtain ⟨z, hz, hY⟩ := primitivePart_isPrimitive M J
  exact ⟨z, hz, hY⟩

/-! ## Fractional invertibility -/

theorem primitivePart_fractional_isUnit
    (J : Ideal (CoordinateRing M))
    (hJ :
      IsUnit
        (J :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) :
    IsUnit
      (primitivePart M J (contentGenerator M J) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  have hmul :
      IsUnit (
        ((Ideal.span
              ({xClass M (contentGenerator M J)} :
                Set (CoordinateRing M)) :
              Ideal (CoordinateRing M)) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) *
          (primitivePart M J (contentGenerator M J) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))) := by
    rw [← FractionalIdeal.coeIdeal_mul,
      span_content_mul_primitivePart M J]
    exact hJ
  exact (IsUnit.mul_iff.mp hmul).2

theorem primitivePart_fractional_eq
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    (primitivePart M J (contentGenerator M J) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      ((Ideal.span
            ({xClass M (contentGenerator M J)} :
              Set (CoordinateRing M)) :
            Ideal (CoordinateRing M)) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M))⁻¹ *
        (J :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
  let d := contentGenerator M J
  let P : Ideal (CoordinateRing M) :=
    Ideal.span ({xClass M d} : Set (CoordinateRing M))
  let J₀ : Ideal (CoordinateRing M) := primitivePart M J d
  have hd : d ≠ 0 := contentGenerator_ne_zero M J hJ
  have hbase : xClass M d ≠ 0 := xClass_ne_zero M hd
  have hPJ : P * J₀ = J := by
    exact span_content_mul_primitivePart M J
  calc
    (J₀ : FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M)) =
        1 * (J₀ : FractionalIdeal
          (CoordinateRing M)⁰ (FunctionField M)) := by simp
    _ = ((P :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))⁻¹ *
          (P :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))) *
        (J₀ :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
      rw [FractionalIdeal.coe_ideal_span_singleton_inv_mul
        (FunctionField M) hbase]
    _ = (P :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))⁻¹ *
        ((P :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) *
          (J₀ :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))) := by
      rw [mul_assoc]
    _ = (P :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))⁻¹ *
        (J :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
      rw [← FractionalIdeal.coeIdeal_mul, hPJ]

/-! ## Oriented primitive representatives -/

def contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M d))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hd))

@[simp] theorem coe_contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (contentFunctionUnit M d hd : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M d) := rfl

namespace IntegralOrientedRep

variable (O : InfinityOrder M)

def primitivePartUnit (R : IntegralOrientedRep M) : InvFrac M :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit

@[simp] theorem coe_primitivePartUnit
    (R : IntegralOrientedRep M) :
    (R.primitivePartUnit M :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      primitivePart M R.ideal (contentGenerator M R.ideal) :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit_spec

def contentUnit (R : IntegralOrientedRep M) :
    (FunctionField M)ˣ :=
  contentFunctionUnit M (contentGenerator M R.ideal)
    (contentGenerator_ne_zero M R.ideal (R.ideal_ne_bot M))

/-- Divide the integral ideal by its polynomial content and adjust the
stored orientation by the exact `ordPlus` of that principal factor. -/
def primitivePartRep (R : IntegralOrientedRep M) :
    IntegralOrientedRep M where
  ideal := primitivePart M R.ideal (contentGenerator M R.ideal)
  unit := R.primitivePartUnit M
  coe_unit := coe_primitivePartUnit M R
  atInfinity :=
    R.atInfinity -
      Multiplicative.toAdd (O.ordPlus (R.contentUnit M))

@[simp] theorem primitivePartRep_ideal
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).ideal =
      primitivePart M R.ideal (contentGenerator M R.ideal) := rfl

@[simp] theorem primitivePartRep_atInfinity
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).atInfinity =
      R.atInfinity -
        Multiplicative.toAdd (O.ordPlus (R.contentUnit M)) := rfl

theorem primitivePartRep_isPrimitive
    (R : IntegralOrientedRep M) :
    IdealIsPrimitive M (R.primitivePartRep M O).ideal :=
  primitivePart_isPrimitive M R.ideal

theorem primitivePartUnit_mul_contentUnit
    (R : IntegralOrientedRep M) :
    R.primitivePartUnit M *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (R.contentUnit M) =
      R.unit := by
  apply Units.ext
  simp only [Units.val_mul, coe_primitivePartUnit,
    coe_toPrincipalIdeal, contentUnit,
    coe_contentFunctionUnit]
  calc
    (primitivePart M R.ideal (contentGenerator M R.ideal) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) *
        FractionalIdeal.spanSingleton
          (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M (contentGenerator M R.ideal))) =
      (primitivePart M R.ideal (contentGenerator M R.ideal) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) *
        (Ideal.span
            ({xClass M (contentGenerator M R.ideal)} :
              Set (CoordinateRing M)) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
              rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        ((Ideal.span
              ({xClass M (contentGenerator M R.ideal)} :
                Set (CoordinateRing M)) :
            Ideal (CoordinateRing M)) *
          primitivePart M R.ideal (contentGenerator M R.ideal) :
          Ideal (CoordinateRing M)) := by
            rw [FractionalIdeal.coeIdeal_mul]
            ac_rfl
    _ = (R.ideal :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
              rw [span_content_mul_primitivePart M R.ideal]
    _ = (R.unit :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := R.coe_unit.symm

/-- Removing content is an exact principal equivalence in the oriented
quotient, not merely an equality of unoriented ideal classes. -/
theorem primitivePartRep_picClass
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).picClass M O =
      R.picClass M O := by
  change
    QuotientGroup.mk' (principalOriented M O).range
        ((R.primitivePartRep M O).raw M) =
      QuotientGroup.mk' (principalOriented M O).range (R.raw M)
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨principalOriented M O (R.contentUnit M),
    MonoidHom.mem_range.mpr ⟨R.contentUnit M, rfl⟩, ?_⟩
  apply Prod.ext
  · exact primitivePartUnit_mul_contentUnit M R
  · change
      Multiplicative.ofAdd
          (R.atInfinity -
            Multiplicative.toAdd
              (O.ordPlus (R.contentUnit M))) *
        O.ordPlus (R.contentUnit M) =
      Multiplicative.ofAdd R.atInfinity
    change
      R.atInfinity -
          Multiplicative.toAdd
            (O.ordPlus (R.contentUnit M)) +
        Multiplicative.toAdd
          (O.ordPlus (R.contentUnit M)) =
      R.atInfinity
    omega

end IntegralOrientedRep

/-- Every oriented Picard class has a primitive integral representative.
This closes the missing bridge between denominator clearing and Mumford
graph extraction. -/
theorem exists_primitiveIntegralRepresentative
    (O : InfinityOrder M) (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M,
      IdealIsPrimitive M R.ideal ∧ R.picClass M O = c := by
  obtain ⟨R, hR⟩ := exists_integralRepresentative M O c
  refine ⟨R.primitivePartRep M O,
    R.primitivePartRep_isPrimitive M O, ?_⟩
  exact (R.primitivePartRep_picClass M O).trans hR

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticFunctionConjugation
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Hyperelliptic conjugation on the sextic function field

The affine involution `Y ↦ -Y` extends functorially from the coordinate ring
to the fraction field.  Packaging it as a ring equivalence makes conjugation
of units and fractional ideals available without choosing numerators and
denominators.
-/

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

def conjugateEquiv (M : Model K) :
    CoordinateRing M ≃+* CoordinateRing M where
  toFun := conjugate M
  invFun := conjugate M
  left_inv := conjugate_involutive M
  right_inv := conjugate_involutive M
  map_mul' := map_mul (conjugate M)
  map_add' := map_add (conjugate M)

@[simp] theorem conjugateEquiv_apply (M : Model K)
    (z : CoordinateRing M) :
    conjugateEquiv M z = conjugate M z := rfl

@[simp] theorem conjugateEquiv_symm (M : Model K) :
    (conjugateEquiv M).symm = conjugateEquiv M := by
  rfl

def functionConjugateEquiv (M : Model K) :
    FunctionField M ≃+* FunctionField M :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField M)
    (L := FunctionField M) (conjugateEquiv M)

@[simp] theorem functionConjugateEquiv_algebraMap
    (M : Model K) (z : CoordinateRing M) :
    functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M) (FunctionField M) (conjugate M z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (conjugateEquiv M) z

@[simp] theorem functionConjugateEquiv_symm (M : Model K) :
    (functionConjugateEquiv M).symm = functionConjugateEquiv M := by
  rw [functionConjugateEquiv,
    IsFractionRing.ringEquivOfRingEquiv_symm, conjugateEquiv_symm]

theorem functionConjugate_involutive (M : Model K) :
    Function.Involutive (functionConjugateEquiv M) := by
  intro z
  simpa only [functionConjugateEquiv_symm] using
    (functionConjugateEquiv M).symm_apply_apply z

def conjugateFunctionUnit (M : Model K) :
    (FunctionField M)ˣ →* (FunctionField M)ˣ :=
  Units.map (functionConjugateEquiv M).toRingHom

@[simp] theorem conjugateFunctionUnit_val (M : Model K)
    (z : (FunctionField M)ˣ) :
    (conjugateFunctionUnit M z : FunctionField M) =
      functionConjugateEquiv M (z : FunctionField M) := rfl

theorem conjugateFunctionUnit_involutive (M : Model K) :
    Function.Involutive (conjugateFunctionUnit M) := by
  intro z
  apply Units.ext
  exact functionConjugate_involutive M (z : FunctionField M)

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Conjugation of Mumford ideals

Hyperelliptic conjugation sends `(u, Y-v)` to `(u, Y+v)`.  The following lifts
that elementary generator identity to integral and fractional ideals.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem map_conjugate_mumfordIdeal (M : Model K) (u v : K[X]) :
    Ideal.map (conjugate M) (mumfordIdeal M u v) =
      mumfordIdeal M u (-v) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change conjugate M (xClass M u) ∈ mumfordIdeal M u (-v)
      rw [conjugate_xClass]
      exact xClass_mem_mumfordIdeal M u (-v)
    · change conjugate M (ySubClass M v) ∈ mumfordIdeal M u (-v)
      have htarget : ySubClass M (-v) ∈ mumfordIdeal M u (-v) :=
        ySubClass_mem_mumfordIdeal M u (-v)
      have heq :
          conjugate M (ySubClass M v) = -ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [heq]
      exact (mumfordIdeal M u (-v)).neg_mem htarget
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using Ideal.mem_map_of_mem (conjugate M)
        (xClass_mem_mumfordIdeal M u v)
    · have hsource :
          -ySubClass M v ∈ mumfordIdeal M u v :=
        (mumfordIdeal M u v).neg_mem
          (ySubClass_mem_mumfordIdeal M u v)
      have hmap := Ideal.mem_map_of_mem (conjugate M) hsource
      have heq :
          conjugate M (-ySubClass M v) = ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [← heq]
      exact hmap

def conjugateFractionalIdealEquiv (M : Model K) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) ≃+*
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) :=
  FractionalIdeal.ringEquivOfRingEquiv
    (FunctionField M) (FunctionField M) (conjugateEquiv M)

theorem conjugateFractionalIdealEquiv_coeIdeal
    (M : Model K) (I : Ideal (CoordinateRing M)) :
    conjugateFractionalIdealEquiv M
        (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.map (conjugate M) I :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  ext x
  simp only [conjugateFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjugate M a, Ideal.mem_map_of_mem (conjugate M) ha, ?_⟩
    change algebraMap (CoordinateRing M) (FunctionField M)
        (conjugate M a) =
      functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a)
    exact (functionConjugateEquiv_algebraMap M a).symm
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_iff_of_surjective (conjugate M)
      (conjugate_involutive M).surjective] at hb
    obtain ⟨a, ha, hab⟩ := hb
    refine ⟨algebraMap (CoordinateRing M) (FunctionField M) a,
      FractionalIdeal.mem_coeIdeal_of_mem _ ha, ?_⟩
    change functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a) =
      algebraMap (CoordinateRing M) (FunctionField M) b
    rw [functionConjugateEquiv_algebraMap, hab]

@[simp] theorem conjugateFractionalIdealEquiv_mumfordIdeal
    (M : Model K) (u v : K[X]) :
    conjugateFractionalIdealEquiv M
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M u (-v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [conjugateFractionalIdealEquiv_coeIdeal,
    map_conjugate_mumfordIdeal]

@[simp] theorem conjugateFractionalIdealEquiv_spanSingleton
    (M : Model K) (z : FunctionField M) :
    conjugateFractionalIdealEquiv M
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰ z) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (functionConjugateEquiv M z) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FunctionField M) (FunctionField M) (conjugateEquiv M) z

def conjugateInvFrac (M : Model K) : InvFrac M →* InvFrac M :=
  Units.map (conjugateFractionalIdealEquiv M).toRingHom

@[simp] theorem conjugateInvFrac_principal
    (M : Model K) (z : (FunctionField M)ˣ) :
    conjugateInvFrac M
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) z) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (conjugateFunctionUnit M z) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      ((toPrincipalIdeal (CoordinateRing M) (FunctionField M) z :
        InvFrac M) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((toPrincipalIdeal (CoordinateRing M) (FunctionField M)
      (conjugateFunctionUnit M z) : InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    conjugateFractionalIdealEquiv_spanSingleton,
    conjugateFunctionUnit_val]

def conjugateSemiMumford (M : Model K) (D : SemiMumford M) :
    SemiMumford M where
  u := D.u
  v := -D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := by
    rw [← Polynomial.modByMonic_eq_mod (-D.v) D.u_monic,
      Polynomial.neg_modByMonic,
      Polynomial.modByMonic_eq_mod D.v D.u_monic,
      D.v_reduced]
  curve_dvd := by
    simpa only [neg_sq] using D.curve_dvd

@[simp] theorem conjugateSemiMumford_u (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).u = D.u := rfl

@[simp] theorem conjugateSemiMumford_v (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).v = -D.v := rfl

@[simp] theorem conjugateInvFrac_mumfordIdealUnit
    (M : Model K) (D : SemiMumford M) :
    conjugateInvFrac M (mumfordIdealUnit M D) =
      mumfordIdealUnit M (conjugateSemiMumford M D) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    (mumfordIdeal M D.u (-D.v) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [conjugateFractionalIdealEquiv_mumfordIdeal]

theorem conjugate_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (z : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) z =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M (conjugateSemiMumford M D₁) *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (conjugateFunctionUnit M z) =
        mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
  have hmap := congrArg (conjugateInvFrac M) h
  simpa only [map_mul, conjugateInvFrac_mumfordIdealUnit,
    conjugateInvFrac_principal] using hmap

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordCantorReduction
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# One-step Cantor reduction for a monic sextic

This file isolates the structural algebra used by a well-founded Cantor
reduction.  It contains no enumeration and no Riemann--Roch input.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

local instance instDecidableEq_fLT : DecidableEq K := Classical.decEq K

/-! ## Changing the graph polynomial modulo `u` -/

/-- Replacing `v` by a congruent polynomial modulo `u` does not change the
Mumford ideal. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v V : K[X]) (h : u ∣ V - v) :
    mumfordIdeal M u V = mumfordIdeal M u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u v
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u v := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u v)
      have heq :
          ySubClass M V =
            ySubClass M v - xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal M u v) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u V
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u V := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u V)
      have heq :
          ySubClass M v =
            ySubClass M V + xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal M u V) hmultiple

theorem mumfordIdeal_add_mul
    (u v t : K[X]) :
    mumfordIdeal M u (v + u * t) = mumfordIdeal M u v := by
  apply mumfordIdeal_eq_of_dvd_sub
  refine ⟨t, ?_⟩
  ring

/-- Multiplying the first generator by a polynomial unit does not change a
Mumford ideal.  The divisibility formulation avoids choosing that unit. -/
theorem mumfordIdeal_eq_of_dvd_dvd
    (u u' v : K[X]) (huu' : u ∣ u') (hu'u : u' ∣ u) :
    mumfordIdeal M u v = mumfordIdeal M u' v := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := hu'u
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u' v)
    · exact ySubClass_mem_mumfordIdeal M u' v
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := huu'
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u v)
    · exact ySubClass_mem_mumfordIdeal M u v

theorem mumfordIdeal_normalize
    (u v : K[X]) :
    mumfordIdeal M (normalize u) v = mumfordIdeal M u v := by
  exact mumfordIdeal_eq_of_dvd_dvd M (normalize u) u v
    (associated_normalize u).symm.dvd
    (associated_normalize u).dvd

/-! ## The Cantor product identity -/

/-- The ideal product at the heart of one Cantor reduction step.

The Bezout condition is exactly the one supplied by `mumford_bezout` for
the semireduced pair `(u,V)` when `w = (f-V²)/u`. -/
theorem mumfordIdeal_mul_cantor
    (u w V : K[X])
    (hcurve : M.f - V ^ 2 = u * w)
    (hbezout :
      ∃ a b c : K[X],
        a * u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M u V * mumfordIdeal M w V =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M u V
  let J := mumfordIdeal M w V
  let g := ySubClass M V
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hfactor :
          xClass M u * xClass M w =
            ySubClass M V * (yClass M + xClass M V) := by
        symm
        calc
          ySubClass M V * (yClass M + xClass M V) =
              xClass M (M.f - V ^ 2) := by
            simp only [ySubClass]
            calc
              (yClass M - xClass M V) *
                  (yClass M + xClass M V) =
                  yClass M ^ 2 - xClass M V ^ 2 := by ring
              _ = xClass M M.f - xClass M V ^ 2 := by
                rw [yClass_sq]
              _ = xClass M (M.f - V ^ 2) := by
                rw [xClass_sub, xClass_pow]
          _ = xClass M (u * w) := by rw [hcurve]
          _ = xClass M u * xClass M w := by rw [xClass_mul]
      rw [hfactor]
      exact Ideal.mul_mem_right (yClass M + xClass M V) _
        (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (xClass M u) (Ideal.subset_span (Set.mem_singleton _))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass M w) (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (ySubClass M V) (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := hbezout
    have huI : xClass M u ∈ I :=
      xClass_mem_mumfordIdeal M u V
    have hwJ : xClass M w ∈ J :=
      xClass_mem_mumfordIdeal M w V
    have hgI : g ∈ I :=
      ySubClass_mem_mumfordIdeal M u V
    have hgJ : g ∈ J :=
      ySubClass_mem_mumfordIdeal M w V
    have hug : xClass M u * g ∈ I * J :=
      Ideal.mul_mem_mul huI hgJ
    have hgw : g * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul hgI hwJ
    have hgg : g * g ∈ I * J :=
      Ideal.mul_mem_mul hgI hgJ
    have huw : xClass M u * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul huI hwJ
    have htwoVg : xClass M (2 * V) * g ∈ I * J := by
      have hdifference := Ideal.sub_mem (I * J) huw hgg
      convert hdifference using 1
      change
        xClass M (2 * V) * ySubClass M V =
          xClass M u * xClass M w -
            ySubClass M V * ySubClass M V
      have hxTwo :
          xClass M (2 : K[X]) = (2 : CoordinateRing M) := by
        exact map_natCast (xClassHom M) 2
      calc
        xClass M (2 * V) * ySubClass M V =
            xClass M (M.f - V ^ 2) -
              ySubClass M V ^ 2 := by
          simp only [ySubClass]
          rw [show xClass M (M.f - V ^ 2) =
            yClass M ^ 2 - xClass M V ^ 2 by
              rw [yClass_sq, xClass_sub, xClass_pow]]
          simp only [xClass_mul]
          rw [hxTwo]
          ring
        _ = xClass M (u * w) -
              ySubClass M V ^ 2 := by rw [hcurve]
        _ = xClass M u * xClass M w -
              ySubClass M V * ySubClass M V := by
          rw [xClass_mul, pow_two]
    have ha : xClass M a * (xClass M u * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M a) hug
    have hb : xClass M b * (xClass M (2 * V) * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M b) htwoVg
    have hc : xClass M c * (g * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M c) hgw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M u * g) +
            xClass M b * (xClass M (2 * V) * g) +
            xClass M c * (g * xClass M w) = g := by
      calc
        _ = xClass M
              (a * u + b * (2 * V) + c * w) * g := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = g := by rw [hbez, xClass_one, one_mul]
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_cantor_of_semi
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w) :
    mumfordIdeal M D.u D.v * mumfordIdeal M w D.v =
      Ideal.span ({ySubClass M D.v} : Set (CoordinateRing M)) := by
  obtain ⟨w', a, b, c, hw', hbez⟩ := mumford_bezout M D
  have hwEq : w' = w := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    exact hw'.symm.trans hcurve
  subst w'
  exact mumfordIdeal_mul_cantor M D.u w D.v hcurve
    ⟨a, b, c, hbez⟩

/-- Bezout transvection for the graph change `v ↦ v + u t`.  It is the
algebraic reason that the cubic boundary step needs no new coprimality
argument. -/
theorem cantorBezout_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * (D.v + D.u * t)) + c * w = 1 := by
  obtain ⟨w₀, a, b, c, hw₀, hbez⟩ := mumford_bezout M D
  have hwEq :
      w₀ = w + 2 * D.v * t + D.u * t ^ 2 := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    calc
      D.u * w₀ = M.f - D.v ^ 2 := hw₀.symm
      _ = (M.f - (D.v + D.u * t) ^ 2) +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by ring
      _ = D.u * w +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by rw [hcurve]
      _ = D.u * (w + 2 * D.v * t + D.u * t ^ 2) := by ring
  refine ⟨a - 2 * b * t - c * t ^ 2, b + c * t, c, ?_⟩
  rw [hwEq] at hbez
  linear_combination hbez

theorem mumfordIdeal_mul_cantor_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M w (D.v + D.u * t) =
      Ideal.span
        ({ySubClass M (D.v + D.u * t)} :
          Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_add_mul M D.u D.v t]
  exact mumfordIdeal_mul_cantor M D.u w
    (D.v + D.u * t) hcurve
    (cantorBezout_add_mul M D t w hcurve)

/-! ## Degree descent -/

/-- A factor in `f - V² = u w` cannot vanish. -/
theorem cantorFactor_ne_zero
    (u V w : K[X]) (hcurve : M.f - V ^ 2 = u * w) :
    w ≠ 0 := by
  intro hw
  have hsub : M.f - V ^ 2 = 0 := by
    simpa [hw] using hcurve
  have hsq : V ^ 2 = M.f := (sub_eq_zero.mp hsub).symm
  have hVunit : IsUnit V := by
    apply M.squarefree V
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hVunit.pow 2
  exact M.not_isUnit hfunit

/-- Above genus two, the quotient in a Cantor step has strictly smaller
degree than the old monic denominator. -/
theorem cantorFactor_natDegree_lt
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    w.natDegree < D.u.natDegree := by
  have hw : w ≠ 0 := cantorFactor_ne_zero M D.u D.v w hcurve
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree : D.v.natDegree < D.u.natDegree := by
    by_cases hv : D.v = 0
    · rw [hv]
      simp
      omega
    · exact natDegree_lt_natDegree hv hvDegree
  have hnum :
      (M.f - D.v ^ 2).natDegree ≤
        max 6 (2 * D.v.natDegree) := by
    calc
      (M.f - D.v ^ 2).natDegree ≤
          max M.f.natDegree (D.v ^ 2).natDegree :=
        natDegree_sub_le _ _
      _ = max 6 (2 * D.v.natDegree) := by
        rw [M.natDegree, natDegree_pow]
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - D.v ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  have hbound :
      max 6 (2 * D.v.natDegree) <
        2 * D.u.natDegree := by
    rw [Nat.max_lt]
    omega
  omega

/-- In the cubic boundary case one replaces `v` by `v + u`.  The leading
terms of `f` and `(v+u)²` then cancel, so the quotient has degree at most
two. -/
theorem cubicCantorFactor
    (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve :
      M.f - (D.v + D.u) ^ 2 = D.u * w) :
    w ≠ 0 ∧ w.natDegree ≤ 2 := by
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hVMonic : (D.v + D.u).Monic :=
    D.u_monic.add_of_right hvDegree
  have hVNatDegree : (D.v + D.u).natDegree = 3 := by
    rw [natDegree_add_eq_right_of_degree_lt hvDegree, hdeg]
  have hf : IsMonicOfDegree M.f 6 :=
    ⟨M.natDegree, M.monic⟩
  have hV : IsMonicOfDegree (D.v + D.u) 3 :=
    ⟨hVNatDegree, hVMonic⟩
  have hV2 : IsMonicOfDegree ((D.v + D.u) ^ 2) 6 := by
    simpa using hV.pow 2
  have hnum :
      (M.f - (D.v + D.u) ^ 2).natDegree < 6 :=
    hf.natDegree_sub_lt (by norm_num) hV2
  have hw : w ≠ 0 :=
    cantorFactor_ne_zero M D.u (D.v + D.u) w hcurve
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - (D.v + D.u) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  constructor
  · exact hw
  · omega

/-! ## The normalized next semirepresentative -/

private theorem normalize_dvd_sub_mod
    (p q : K[X]) :
    normalize q ∣ p - p % normalize q := by
  refine ⟨p / normalize q, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p (normalize q)
  calc
    p - p % normalize q =
        (p % normalize q + normalize q * (p / normalize q)) -
          p % normalize q := by
      rw [hdiv]
    _ = normalize q * (p / normalize q) := by ring

/-- Normalize the quotient and reduce the complementary graph polynomial.
This is the inverse affine class; the actual Cantor successor is its
hyperelliptic conjugate below. -/
def cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w)
    (hw : w ≠ 0) :
    SemiMumford M where
  u := normalize w
  v := V % normalize w
  nInf := n
  u_monic := monic_normalize hw
  v_reduced := by
    apply (mod_eq_self_iff (monic_normalize hw).ne_zero).mpr
    exact degree_mod_lt _ (monic_normalize hw).ne_zero
  curve_dvd := by
    have hnW : normalize w ∣ w :=
      (associated_normalize w).symm.dvd
    have hnBase : normalize w ∣ M.f - V ^ 2 := by
      obtain ⟨c, hc⟩ := hnW
      refine ⟨D.u * c, ?_⟩
      calc
        M.f - V ^ 2 = D.u * w := hcurve
        _ = D.u * (normalize w * c) :=
          congrArg (fun z : K[X] ↦ D.u * z) hc
        _ = normalize w * (D.u * c) := by ring
    have hnGraph :
        normalize w ∣ V - V % normalize w :=
      normalize_dvd_sub_mod V w
    obtain ⟨a, ha⟩ := hnBase
    obtain ⟨b, hb⟩ := hnGraph
    refine ⟨a + b * (V + V % normalize w), ?_⟩
    calc
      M.f - (V % normalize w) ^ 2 =
          (M.f - V ^ 2) +
            (V - V % normalize w) *
              (V + V % normalize w) := by ring
      _ = normalize w * a +
            (normalize w * b) *
              (V + V % normalize w) := by rw [ha, hb]
      _ = normalize w *
            (a + b * (V + V % normalize w)) := by ring

@[simp] theorem cantorComplementSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).u = normalize w := rfl

@[simp] theorem cantorComplementSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).v =
      V % normalize w := rfl

@[simp] theorem cantorComplementSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).nInf = n := rfl

theorem mumfordIdeal_cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorComplementSemi M D V w n hcurve hw).u
        (cantorComplementSemi M D V w n hcurve hw).v =
      mumfordIdeal M w V := by
  change
    mumfordIdeal M (normalize w) (V % normalize w) =
      mumfordIdeal M w V
  calc
    mumfordIdeal M (normalize w) (V % normalize w) =
        mumfordIdeal M (normalize w) V :=
      (mumfordIdeal_eq_of_dvd_sub M (normalize w)
        (V % normalize w) V
        (normalize_dvd_sub_mod V w)).symm
    _ = mumfordIdeal M w V := mumfordIdeal_normalize M w V

theorem mumfordIdeal_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M
          (cantorComplementSemi M D V w n hcurve hw).u
          (cantorComplementSemi M D V w n hcurve hw).v =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_eq_of_dvd_sub M D.u D.v V hcongr,
    mumfordIdeal_cantorComplementSemi M D V w n hcurve hw]
  exact mumfordIdeal_mul_cantor M D.u w V hcurve hbezout

/-! ## Conjugating the complement -/

/-- The affine Cantor successor is the conjugate of the complement.  Its
graph polynomial is `(-V) mod normalize w`, up to the definitional
linearity of polynomial remainder. -/
def cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  conjugateSemiMumford M
    (cantorComplementSemi M D V w n hcurve hw)

@[simp] theorem cantorConjugateSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).u =
      normalize w := rfl

@[simp] theorem cantorConjugateSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      -(V % normalize w) := rfl

theorem cantorConjugateSemi_v_eq_neg_mod
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      (-V) % normalize w := by
  change -(V % normalize w) = (-V) % normalize w
  rw [← Polynomial.modByMonic_eq_mod V (monic_normalize hw),
    ← Polynomial.modByMonic_eq_mod (-V) (monic_normalize hw),
    Polynomial.neg_modByMonic]

@[simp] theorem cantorConjugateSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).nInf = n := rfl

theorem mumfordIdeal_cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorConjugateSemi M D V w n hcurve hw).u
        (cantorConjugateSemi M D V w n hcurve hw).v =
      mumfordIdeal M w (-V) := by
  rw [cantorConjugateSemi_v_eq_neg_mod]
  change
    mumfordIdeal M (normalize w) ((-V) % normalize w) =
      mumfordIdeal M w (-V)
  calc
    mumfordIdeal M (normalize w) ((-V) % normalize w) =
        mumfordIdeal M (normalize w) (-V) :=
      (mumfordIdeal_eq_of_dvd_sub M (normalize w)
        ((-V) % normalize w) (-V)
        (normalize_dvd_sub_mod (-V) w)).symm
    _ = mumfordIdeal M w (-V) :=
      mumfordIdeal_normalize M w (-V)

/-! ## Principal functions in one oriented step -/

theorem ySubClass_ne_zero (V : K[X]) :
    ySubClass M V ≠ 0 := by
  intro h
  have hcoeff : (1 : K[X]) = 0 := by
    simpa using congrArg (coeffY M) h
  exact one_ne_zero hcoeff

def ySubFunctionUnit (V : K[X]) : (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (ySubClass M V))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (ySubClass_ne_zero M V))

@[simp] theorem coe_ySubFunctionUnit (V : K[X]) :
    (ySubFunctionUnit M V : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (ySubClass M V) := rfl

def xClassFunctionUnit (p : K[X]) (hp : p ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M p))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hp))

@[simp] theorem coe_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    (xClassFunctionUnit M p hp : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M p) := rfl

/-- The principal correction taking the conjugate complement back to the
original affine ideal class: `(Y-V) / normalize(w)`. -/
def cantorCorrectionUnit
    (V w : K[X]) (hw : w ≠ 0) :
    (FunctionField M)ˣ :=
  ySubFunctionUnit M V *
    (xClassFunctionUnit M (normalize w)
      (monic_normalize hw).ne_zero)⁻¹

theorem mumfordIdealUnit_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M D *
        mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (ySubFunctionUnit M V) := by
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_cantorComplement M D V w n hcurve hw
      hcongr hbezout,
    FractionalIdeal.coeIdeal_span_singleton]

theorem mumfordIdealUnit_complement_mul_conjugate
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) *
        mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (xClassFunctionUnit M (normalize w)
          (monic_normalize hw).ne_zero) := by
  let E := cantorComplementSemi M D V w n hcurve hw
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_xClassFunctionUnit]
  change
    (mumfordIdeal M E.u E.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M E.u (-E.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (algebraMap (CoordinateRing M) (FunctionField M)
          (xClass M E.u))
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_conj_integral M E,
    FractionalIdeal.coeIdeal_span_singleton]

theorem cantorConjugateSemi_principalRelation
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (cantorCorrectionUnit M V w hw) =
      mumfordIdealUnit M D := by
  have hprod :=
    mumfordIdealUnit_mul_cantorComplement M D V w n
      hcurve hw hcongr hbezout
  have hnorm :=
    mumfordIdealUnit_complement_mul_conjugate M D V w n
      hcurve hw
  rw [cantorCorrectionUnit, map_mul, map_inv]
  calc
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (ySubFunctionUnit M V) *
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (xClassFunctionUnit M (normalize w)
              (monic_normalize hw).ne_zero))⁻¹) =
      mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        ((mumfordIdealUnit M D *
            mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw)) *
          (mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw) *
            mumfordIdealUnit M
              (cantorConjugateSemi M D V w n hcurve hw))⁻¹) := by
        rw [hprod, hnorm]
    _ = mumfordIdealUnit M D := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-! ## Exact oriented update -/

/-- The raw oriented class attached to an integral semirepresentative.  The
`-1` agrees exactly with `mumfordRaw` on balanced representatives. -/
def semiMumfordRaw (D : SemiMumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D,
    Multiplicative.ofAdd (D.nInf - 1))

def semiMumfordClass (O : InfinityOrder M) (D : SemiMumford M) :
    OrientedPic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range
      (semiMumfordRaw M D)

theorem semiMumfordClass_eq_iff
    (O : InfinityOrder M) (D₁ D₂ : SemiMumford M) :
    semiMumfordClass M O D₁ = semiMumfordClass M O D₂ ↔
      ∃ alpha : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁ *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M)
                alpha =
            mumfordIdealUnit M D₂ ∧
        Multiplicative.ofAdd (D₁.nInf - 1) *
              O.ordPlus alpha =
            Multiplicative.ofAdd (D₂.nInf - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₁) =
    QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨alpha, congrArg Prod.fst hmul, congrArg Prod.snd hmul⟩
  · rintro ⟨alpha, hIdeal, hInf⟩
    refine ⟨principalOriented M O alpha,
      MonoidHom.mem_range.mpr ⟨alpha, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

@[simp] theorem semiMumfordClass_toSemi
    (O : InfinityOrder M) (D : Mumford M) :
    semiMumfordClass M O D.toSemi = classOf M O D := rfl

/-- The unique integer correction forced by the order of the principal
function `(Y-V)/normalize(w)` at the chosen positive infinity. -/
def cantorNextNInf
    (O : InfinityOrder M) (D : SemiMumford M)
    (V w : K[X]) (hw : w ≠ 0) : ℤ :=
  D.nInf -
    Multiplicative.toAdd
      (O.ordPlus (cantorCorrectionUnit M V w hw))

/-- One structurally complete Cantor step, including the sign of the next
graph polynomial and the exact oriented-infinity correction. -/
def cantorNextSemi
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  cantorConjugateSemi M D V w
    (cantorNextNInf M O D V w hw) hcurve hw

@[simp] theorem cantorNextSemi_u
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u = normalize w := rfl

theorem cantorNextSemi_v
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).v =
      (-V) % normalize w :=
  cantorConjugateSemi_v_eq_neg_mod M D V w
    (cantorNextNInf M O D V w hw) hcurve hw

@[simp] theorem cantorNextSemi_nInf
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).nInf =
      D.nInf -
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) := rfl

theorem cantorNextSemi_class
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    semiMumfordClass M O
        (cantorNextSemi M O D V w hcurve hw) =
      semiMumfordClass M O D := by
  apply (semiMumfordClass_eq_iff M O
    (cantorNextSemi M O D V w hcurve hw) D).2
  refine ⟨cantorCorrectionUnit M V w hw, ?_, ?_⟩
  · exact cantorConjugateSemi_principalRelation M D V w
      (cantorNextNInf M O D V w hw) hcurve hw hcongr hbezout
  · change
      Multiplicative.ofAdd
          (D.nInf -
              Multiplicative.toAdd
                (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1) *
          O.ordPlus (cantorCorrectionUnit M V w hw) =
        Multiplicative.ofAdd (D.nInf - 1)
    change
      D.nInf -
          Multiplicative.toAdd
            (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1 +
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) =
      D.nInf - 1
    omega

theorem natDegree_normalize_eq
    (p : K[X]) :
    (normalize p).natDegree = p.natDegree := by
  exact natDegree_eq_natDegree degree_normalize

@[simp] theorem cantorNextSemi_natDegree
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u.natDegree =
      w.natDegree := by
  rw [cantorNextSemi_u, natDegree_normalize_eq]

theorem cantorBezout_of_semi_factor
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  obtain ⟨w', a, b, c, hw', hbez⟩ := mumford_bezout M D
  have hwEq : w' = w := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    exact hw'.symm.trans hcurve
  subst w'
  exact ⟨a, b, c, hbez⟩

/-- The ordinary branch of the degree step preserves the oriented class
and strictly decreases degree whenever the current degree exceeds three. -/
theorem cantorNextSemi_sameGraph
    (O : InfinityOrder M) (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    semiMumfordClass M O
          (cantorNextSemi M O D D.v w hcurve
            (cantorFactor_ne_zero M D.u D.v w hcurve)) =
        semiMumfordClass M O D ∧
      (cantorNextSemi M O D D.v w hcurve
          (cantorFactor_ne_zero M D.u D.v w hcurve)).u.natDegree <
        D.u.natDegree := by
  let hw := cantorFactor_ne_zero M D.u D.v w hcurve
  constructor
  · apply cantorNextSemi_class M O D D.v w hcurve hw
    · simp
    · exact cantorBezout_of_semi_factor M D w hcurve
  · rw [cantorNextSemi_natDegree]
    exact cantorFactor_natDegree_lt M D w hcurve hdeg

/-- At degree three, the monic lift `V=v+u` preserves the oriented class
and lands directly in affine degree at most two. -/
theorem cantorNextSemi_cubic
    (O : InfinityOrder M) (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve : M.f - (D.v + D.u) ^ 2 = D.u * w) :
    semiMumfordClass M O
          (cantorNextSemi M O D (D.v + D.u) w hcurve
            (cubicCantorFactor M D w hdeg hcurve).1) =
        semiMumfordClass M O D ∧
      (cantorNextSemi M O D (D.v + D.u) w hcurve
          (cubicCantorFactor M D w hdeg hcurve).1).u.natDegree ≤ 2 := by
  let hw := (cubicCantorFactor M D w hdeg hcurve).1
  constructor
  · apply cantorNextSemi_class M O D (D.v + D.u) w hcurve hw
    · refine ⟨1, ?_⟩
      ring
    · simpa using cantorBezout_add_mul M D 1 w (by simpa using hcurve)
  · rw [cantorNextSemi_natDegree]
    exact (cubicCantorFactor M D w hdeg hcurve).2

end

end MazurProof.SexticMumford


end

section
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
# Structural reduction of oriented sextic ideals

This file joins the two algebraic seams:

* polynomial-content division produces a primitive integral ideal;
* primitive integral ideals have semi-Mumford graph form.

It then packages the well-founded affine-degree step.  Infinity balancing
is deliberately a separate phase.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

theorem IntegralOrientedRep.exists_semiMumford
    (R : IntegralOrientedRep M)
    (hprimitive : IdealIsPrimitive M R.ideal) :
    ∃ D : SemiMumford M,
      semiMumfordClass M O D = R.picClass M O ∧
      mumfordIdeal M D.u D.v = R.ideal := by
  obtain ⟨D, hIdeal, -, hn⟩ :=
    exists_semiMumford_of_primitive M R.ideal
      (R.ideal_ne_bot M) hprimitive (R.atInfinity + 1)
  have hunit : mumfordIdealUnit M D = R.unit := by
    apply Units.ext
    rw [coe_mumfordIdealUnit, hIdeal, ← R.coe_unit]
  have hraw : semiMumfordRaw M D = R.raw M := by
    apply Prod.ext
    · exact hunit
    · change
        Multiplicative.ofAdd (D.nInf - 1) =
          Multiplicative.ofAdd R.atInfinity
      congr 1
      rw [hn]
      omega
  refine ⟨D, ?_, hIdeal⟩
  change
    Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (semiMumfordRaw M D)) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (R.raw M))
  rw [hraw]

/-- Every oriented class has a semi-Mumford representative before any
degree reduction. -/
theorem exists_semiMumfordRepresentative
    (c : ConcretePic M O) :
    ∃ D : SemiMumford M, semiMumfordClass M O D = c := by
  obtain ⟨R, hprimitive, hR⟩ :=
    exists_primitiveIntegralRepresentative M O c
  obtain ⟨D, hD, -⟩ :=
    R.exists_semiMumford M O hprimitive
  exact ⟨D, hD.trans hR⟩

/-! ## A canonical affine-degree step -/

/-- The quotient already supplied by the divisibility field of a
semi-Mumford representative. -/
def semiFactor (D : SemiMumford M) : K[X] :=
  Classical.choose D.curve_dvd

theorem semiFactor_spec (D : SemiMumford M) :
    M.f - D.v ^ 2 = D.u * semiFactor M D :=
  Classical.choose_spec D.curve_dvd

/-- At degree three use the monic lift `v+u`; otherwise use the reduced
graph polynomial itself. -/
def degreeLift (D : SemiMumford M) : K[X] :=
  if D.u.natDegree = 3 then D.v + D.u else D.v

theorem degreeLift_congr (D : SemiMumford M) :
    D.u ∣ degreeLift M D - D.v := by
  unfold degreeLift
  split_ifs
  · refine ⟨1, ?_⟩
    ring
  · simp

theorem degreeLift_curve_dvd (D : SemiMumford M) :
    D.u ∣ M.f - (degreeLift M D) ^ 2 := by
  unfold degreeLift
  split_ifs
  · obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨w - 2 * D.v - D.u, ?_⟩
    calc
      M.f - (D.v + D.u) ^ 2 =
          (M.f - D.v ^ 2) -
            2 * D.u * D.v - D.u ^ 2 := by ring
      _ = D.u * w - 2 * D.u * D.v - D.u ^ 2 := by
            rw [hw]
      _ = D.u * (w - 2 * D.v - D.u) := by ring
  · exact D.curve_dvd

def degreeStepFactor (D : SemiMumford M) : K[X] :=
  Classical.choose (degreeLift_curve_dvd M D)

theorem degreeStepFactor_spec (D : SemiMumford M) :
    M.f - (degreeLift M D) ^ 2 =
      D.u * degreeStepFactor M D :=
  Classical.choose_spec (degreeLift_curve_dvd M D)

theorem degreeStepFactor_ne_zero (D : SemiMumford M) :
    degreeStepFactor M D ≠ 0 :=
  cantorFactor_ne_zero M D.u (degreeLift M D)
    (degreeStepFactor M D) (degreeStepFactor_spec M D)

def degreeStep
    (D : SemiMumford M) :
    SemiMumford M :=
  cantorNextSemi M O D (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)

theorem degreeStep_class
    (D : SemiMumford M) :
    semiMumfordClass M O (degreeStep M O D) =
      semiMumfordClass M O D := by
  unfold degreeStep
  apply cantorNextSemi_class M O D
    (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)
    (degreeLift_congr M D)
  unfold degreeLift
  split_ifs with hdeg
  · simpa using
      cantorBezout_add_mul M D 1 (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)
  · simpa using
      cantorBezout_of_semi_factor M D (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)

theorem degreeStep_lt
    (D : SemiMumford M) (hlarge : 2 < D.u.natDegree) :
    (degreeStep M O D).u.natDegree < D.u.natDegree := by
  unfold degreeStep
  rw [cantorNextSemi_natDegree]
  by_cases hthree : D.u.natDegree = 3
  · have hspec :
        M.f - (D.v + D.u) ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    have hle :=
      (cubicCantorFactor M D (degreeStepFactor M D) hthree
        hspec).2
    omega
  · have hspec :
        M.f - D.v ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    apply cantorFactor_natDegree_lt M D
      (degreeStepFactor M D) hspec
    omega

/-- A semi-Mumford representative together with the terminal affine degree
bound.  This does not yet impose the independent infinity-balance bounds. -/
structure LowDegreeSemi where
  toSemi : SemiMumford M
  degree_le_two : toSemi.u.natDegree ≤ 2

def reduceDegree (D : SemiMumford M) : LowDegreeSemi M :=
  if hsmall : D.u.natDegree ≤ 2 then
    ⟨D, hsmall⟩
  else
    reduceDegree (degreeStep M O D)
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

@[simp] theorem reduceDegree_class
    (D : SemiMumford M) :
    semiMumfordClass M O (reduceDegree M O D).toSemi =
      semiMumfordClass M O D := by
  rw [reduceDegree]
  split_ifs with hsmall
  · rfl
  · rw [reduceDegree_class, degreeStep_class]
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

/-- Phase I of the structural reduction: every oriented class has a
representative of affine degree at most two.  No claim about the independent
`nInf` balance is made here. -/
theorem exists_lowDegreeSemiRepresentative
    (c : ConcretePic M O) :
    ∃ D : LowDegreeSemi M,
      semiMumfordClass M O D.toSemi = c := by
  obtain ⟨D, hD⟩ := exists_semiMumfordRepresentative M O c
  exact ⟨reduceDegree M O D, (reduceDegree_class M O D).trans hD⟩

end

end MazurProof.SexticMumford


end


