-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:54:59.98357+00:00
-- url     : https://prove2.me/theorems/7af368ea-4f27-4a7d-b780-e83d22efb98b
-- title:
--   FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodCoordinateRingTwo_p0
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false




/-!
# Reduction of integral N13 Mumford graphs at two

The good integral equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

has the same coefficients after reduction from `ℤ₂` to `𝔽₂`.  Hence
coefficientwise reduction induces a canonical ring homomorphism between
the two affine coordinate rings.  This file proves that the homomorphism
preserves both coordinates and carries every generalized Mumford graph
ideal exactly to the corresponding special-fibre graph ideal.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordReduction

noncomputable section

abbrev R₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.R₂

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Coefficient reduction from the two-adic integers to `𝔽₂`. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod

/-- Coefficientwise reduction of polynomials in the `X` coordinate. -/
def reducePoly : R₂[X] →+* K[X] :=
  Polynomial.mapRingHom reduceBase

@[simp] theorem reducePoly_apply (p : R₂[X]) :
    reducePoly p = p.map reduceBase := rfl

@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)

@[simp] theorem reduce_hPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.hPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodCoordinateRingTwo.hPoly]

@[simp] theorem reduce_rhsPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodCoordinateRingTwo.rhsPoly]

theorem reduce_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly =
      N13GoodCoordinateRingTwo.curvePoly := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    N13GoodCoordinateRingTwo.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (reducePoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 + C N13GoodCoordinateRingTwo.hPoly * X -
        C N13GoodCoordinateRingTwo.rhsPoly
  rw [reduce_hPoly, reduce_rhsPoly]

private theorem special_curve_dvd :
    N13GoodCoordinateRingTwo.curvePoly ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly := by
  rw [reduce_curvePoly]

/-- Reduction on the affine coordinate ring of the good equation. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_xClass (p : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GoodCoordinateRingTwo.xClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd p

@[simp] theorem reduce_yClass :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GoodCoordinateRingTwo.yClass := by
  exact AdjoinRoot.map_root
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_ySubClass (v : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GoodCoordinateRingTwo.ySubClass (reducePoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass]

/-- Coefficientwise reduction of polynomials is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)

/-- The integral good-model coordinate ring reduces onto its special fibre.
This follows from the common rank-two normal form, not from a presentation
calculation in the quotient. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeffY z)
  refine ⟨
    N13GeneralizedMumfordIntegral.xClass p +
      N13GeneralizedMumfordIntegral.xClass q *
        N13GeneralizedMumfordIntegral.yClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
    hp, hq]
  exact N13GoodCoordinateRingTwo.recompose z

@[simp] theorem reduce_coeff0 (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeff0 z) := by
  calc
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeff0
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeff0_xClass,
        N13GoodCoordinateRingTwo.coeff0_xClass_mul_yClass,
        add_zero]

@[simp] theorem reduce_coeffY (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeffY z) := by
  calc
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeffY
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeffY_xClass,
        N13GoodCoordinateRingTwo.coeffY_xClass_mul_yClass,
        zero_add]

private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : R₂[X]) (hp : reducePoly p = 0) :
    ∃ q : R₂[X], p = C (2 : R₂) * q := by
  have hmem :
      p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Reduction has exactly the vertical principal ideal `(2)` as kernel.
The proof combines the rank-two normal form with the polynomial-map kernel
theorem and the standard description of the maximal ideal of `ℤ₂`. -/
theorem ker_reduceCoordinate :
    RingHom.ker reduceCoordinate =
      Ideal.span
        ({algebraMap R₂ IntegralRing (2 : R₂)} :
          Set IntegralRing) := by
  apply le_antisymm
  · intro z hz
    have hz0 : reduceCoordinate z = 0 :=
      RingHom.mem_ker.mp hz
    have h0 :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) = 0 := by
      rw [← reduce_coeff0 z, hz0]
      simp
    have hY :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) = 0 := by
      rw [← reduce_coeffY z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hY
    rw [Ideal.mem_span_singleton]
    refine ⟨
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass,
      ?_⟩
    rw [← N13GeneralizedMumfordIntegral.recompose z, hp, hq]
    calc
      N13GeneralizedMumfordIntegral.xClass (C 2 * p) +
          N13GeneralizedMumfordIntegral.xClass (C 2 * q) *
            N13GeneralizedMumfordIntegral.yClass =
        N13GeneralizedMumfordIntegral.xClass (C 2) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp only [mul_add,
            N13GeneralizedMumfordIntegral.xClass_mul]
          ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate
      (N13GeneralizedMumfordIntegral.xClass (C (2 : R₂))) = 0
    rw [reduce_xClass]
    simp [reducePoly]

/-- Reduction carries the integral graph ideal onto, rather than merely
into, the graph ideal with reduced coefficients. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly u) (reducePoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal, Ideal.map_span,
    Set.image_pair, reduce_xClass, reduce_ySubClass]

/-- Integral generalized Mumford data carrying the smoothness Bézout
identity.  This is precisely the extra condition needed for the reduced
graph ideal to be invertible. -/
structure SmoothMumford₂ : Type
    extends
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂ where
  bezout :
    ∃ a b c : R₂[X],
      a * u + b * (2 * v +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c * w = 1

/-- The integral graph ideal of smooth two-adic Mumford data has the
expected explicit inverse numerator: its product with the conjugate graph
ideal is the principal ideal `(u)`. -/
theorem integral_mumfordIdeal_mul_conj
    (D : SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v *
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u
          (N13GeneralizedMumfordIntegral.conjugateV D.v) =
      Ideal.span
        ({N13GeneralizedMumfordIntegral.xClass D.u} :
          Set IntegralRing) :=
  N13GeneralizedMumfordIntegral.mumfordIdeal_mul_conj_integral
    D.toSemiMumford D.bezout

/-- Hyperelliptic conjugation commutes with coefficient reduction. -/
theorem reduce_conjugateV
    (v : R₂[X]) :
    reducePoly
        (N13GeneralizedMumfordIntegral.conjugateV v) =
      N13GoodCoordinateRingTwo.conjugateV
        (reducePoly v) := by
  unfold N13GeneralizedMumfordIntegral.conjugateV
    N13GoodCoordinateRingTwo.conjugateV
  rw [map_sub, map_neg, reduce_hPoly]

/-- Smooth integral Mumford data reduce to the already constructed smooth
special-fibre data. -/
def reduceSmoothMumford
    (D : SmoothMumford₂) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := reducePoly D.u
  v := reducePoly D.v
  w := reducePoly D.w
  u_monic := D.u_monic.map reduceBase
  curve_eq := by
    have h := congrArg reducePoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      reduce_hPoly, reduce_rhsPoly] using h
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine ⟨reducePoly a, reducePoly b, reducePoly c, ?_⟩
    have h := congrArg reducePoly habc
    simpa only [map_add, map_mul, map_ofNat, map_one,
      reduce_hPoly] using h

@[simp] theorem reduceSmoothMumford_u
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).u = reducePoly D.u := rfl

@[simp] theorem reduceSmoothMumford_v
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).v = reducePoly D.v := rfl

/-- The exact ideal reduction theorem, now stated for smooth integral data. -/
theorem map_smoothMumfordIdeal
    (D : SmoothMumford₂) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reduceSmoothMumford D).u
        (reduceSmoothMumford D).v := by
  simpa using map_mumfordIdeal D.u D.v

/-- Consequently the reduced graph ideal is represented by the canonical
unit fractional ideal on the special fibre. -/
def reducedIdealUnit
    (D : SmoothMumford₂) :
    N13GoodCoordinateRingTwo.InvFrac :=
  N13GoodCoordinateRingTwo.mumfordIdealUnit
    (reduceSmoothMumford D)

@[simp] theorem coe_reducedIdealUnit
    (D : SmoothMumford₂) :
    (reducedIdealUnit D :
      FractionalIdeal (nonZeroDivisors SpecialRing)
        N13GoodCoordinateRingTwo.FunctionField) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly D.u) (reducePoly D.v) := by
  exact N13GoodCoordinateRingTwo.coe_mumfordIdealUnit
    (reduceSmoothMumford D)

end

end MazurProof.N13GeneralizedMumfordReduction


