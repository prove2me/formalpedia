-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalCurveOverlap_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FormalCurveOverlap_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:40:25.475214+00:00
-- url     : https://prove2.me/theorems/28754432-2bc7-44c1-8731-e0c153abab90
-- title:
--   FLT.Assumptions.MazurProof.N13FormalCurveOverlap source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FormalCurveOverlap

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FormalCurveOverlap
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalLineBundleCech_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0

set_option autoImplicit false




/-!
# The actual formal overlap algebra for the N13 integral curve

The pair multiplication used by the formal Čech calculation is not an
abstract two-dimensional algebra.  It is the normal-form multiplication in
the quadratic algebra

`R₂((t))[v] / (v² + (1+t²+t³)v - (t+t²))`.

This file identifies the two descriptions and constructs the restriction
homomorphism from the actual affine coordinate ring by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

Thus a unit obtained from a genuine local trivialization gives, without any
extra inverse hypothesis, the `NearIdentityTransition` consumed by the
Čech--Nakayama theorem.
-/

open Polynomial

namespace MazurProof.N13FormalCurveOverlap

noncomputable section

open HahnSeries
open scoped LaurentSeries

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalLineBundleCech.R₂

abbrev Laurent : Type :=
  N13FormalLineBundleCech.Laurent₂

abbrev Overlap : Type :=
  N13FormalLineBundleCech.Overlap₂

abbrev IntegralAffineRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

/-- The quadratic equation of the actual formal infinity chart. -/
def formalCurvePoly : Laurent[X] :=
  X ^ 2 +
    Polynomial.C
        (N13FormalLineBundleCech.hInfinity (R := R₂)) * X -
      Polynomial.C
        (N13FormalLineBundleCech.rhsInfinity (R := R₂))

theorem formalCurvePoly_monic :
    formalCurvePoly.Monic := by
  unfold formalCurvePoly
  monicity <;> norm_num

theorem formalCurvePoly_natDegree :
    formalCurvePoly.natDegree = 2 := by
  unfold formalCurvePoly
  compute_degree <;> norm_num

private theorem formalCurvePoly_degree :
    formalCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree formalCurvePoly_monic.ne_zero,
    formalCurvePoly_natDegree]
  norm_num

/-- The actual quadratic algebra on the punctured formal infinity chart. -/
abbrev FormalCurve : Type :=
  AdjoinRoot formalCurvePoly

/-- The formal coordinate `v`. -/
def vClass : FormalCurve :=
  AdjoinRoot.root formalCurvePoly

/-- The canonical normal polynomial of degree below two. -/
def normalPoly :
    FormalCurve →ₗ[Laurent] Laurent[X] :=
  AdjoinRoot.modByMonicHom formalCurvePoly_monic

/-- Scalar coefficient in the basis `1,v`. -/
def coeff0 :
    FormalCurve →ₗ[Laurent] Laurent :=
  (Polynomial.lcoeff Laurent 0).comp normalPoly

/-- `v`-coefficient in the basis `1,v`. -/
def coeffV :
    FormalCurve →ₗ[Laurent] Laurent :=
  (Polynomial.lcoeff Laurent 1).comp normalPoly

/-- Read an actual formal-curve function in the basis `1,v`. -/
def toOverlap :
    FormalCurve →ₗ[Laurent] Overlap where
  toFun z := (coeff0 z, coeffV z)
  map_add' z w := by
    ext <;> simp [coeff0, coeffV, normalPoly]
  map_smul' c z := by
    ext <;> simp [coeff0, coeffV, normalPoly]

/-- Build an actual formal-curve function from its two coefficients. -/
def ofOverlap :
    Overlap →ₗ[Laurent] FormalCurve where
  toFun z :=
    algebraMap Laurent FormalCurve z.1 +
      algebraMap Laurent FormalCurve z.2 * vClass
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' c z := by
    change
      algebraMap Laurent FormalCurve (c * z.1) +
          algebraMap Laurent FormalCurve (c * z.2) * vClass =
        c •
          (algebraMap Laurent FormalCurve z.1 +
            algebraMap Laurent FormalCurve z.2 * vClass)
    simp only [map_mul, Algebra.smul_def]
    ring

theorem normalPoly_eq_C_add_C_mul_X
    (z : FormalCurve) :
    normalPoly z =
      C (coeff0 z) + C (coeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change
        g %ₘ formalCurvePoly =
          C ((g %ₘ formalCurvePoly).coeff 0) +
            C ((g %ₘ formalCurvePoly).coeff 1) * X
      have hsum :=
        Polynomial.sum_modByMonic_coeff
          (p := g) (q := formalCurvePoly)
          formalCurvePoly_monic (n := 2)
          (by rw [formalCurvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Reconstruction from the pair of normal-form coefficients. -/
theorem ofOverlap_toOverlap
    (z : FormalCurve) :
    ofOverlap (toOverlap z) = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        ofOverlap (toOverlap (AdjoinRoot.mk formalCurvePoly g)) =
            AdjoinRoot.mk formalCurvePoly
              (C (coeff0 (AdjoinRoot.mk formalCurvePoly g)) +
                C (coeffV (AdjoinRoot.mk formalCurvePoly g)) * X) := by
                  simp [ofOverlap, toOverlap, vClass,
                    AdjoinRoot.algebraMap_eq]
        _ =
            AdjoinRoot.mk formalCurvePoly
              (normalPoly (AdjoinRoot.mk formalCurvePoly g)) := by
                  rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk formalCurvePoly g :=
          AdjoinRoot.mk_leftInverse formalCurvePoly_monic _

/-- The normal-form coordinates of a pair are the original pair. -/
theorem toOverlap_ofOverlap
    (z : Overlap) :
    toOverlap (ofOverlap z) = z := by
  apply Prod.ext
  · change
      ((C z.1 + C z.2 * X) %ₘ formalCurvePoly).coeff 0 = z.1
    rw [(modByMonic_eq_self_iff formalCurvePoly_monic).mpr]
    · simp
    · rw [formalCurvePoly_degree]
      compute_degree <;> norm_num
  · change
      ((C z.1 + C z.2 * X) %ₘ formalCurvePoly).coeff 1 = z.2
    rw [(modByMonic_eq_self_iff formalCurvePoly_monic).mpr]
    · simp
    · rw [formalCurvePoly_degree]
      compute_degree <;> norm_num

/-- The actual formal curve is linearly equivalent to its coefficient pair. -/
def overlapEquiv :
    FormalCurve ≃ₗ[Laurent] Overlap where
  toFun := toOverlap
  invFun := ofOverlap
  left_inv := ofOverlap_toOverlap
  right_inv := toOverlap_ofOverlap
  map_add' := map_add toOverlap
  map_smul' := map_smul toOverlap

theorem ofOverlap_injective :
    Function.Injective ofOverlap := by
  intro z w hzw
  calc
    z = toOverlap (ofOverlap z) :=
      (toOverlap_ofOverlap z).symm
    _ = toOverlap (ofOverlap w) := by rw [hzw]
    _ = w := toOverlap_ofOverlap w

@[simp] theorem ofOverlap_oneOverlap :
    ofOverlap
        (N13FormalLineBundleCech.oneOverlap (R := R₂)) =
      1 := by
  simp [ofOverlap, N13FormalLineBundleCech.oneOverlap]

/-- The defining quadratic relation of the actual formal curve. -/
theorem vClass_relation :
    vClass ^ 2 +
        algebraMap Laurent FormalCurve
          (N13FormalLineBundleCech.hInfinity (R := R₂)) *
          vClass =
      algebraMap Laurent FormalCurve
        (N13FormalLineBundleCech.rhsInfinity (R := R₂)) := by
  have h := AdjoinRoot.eval₂_root formalCurvePoly
  rw [formalCurvePoly] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul] at h
  exact sub_eq_zero.mp h

/-- Pair multiplication is exactly multiplication in the actual quadratic
formal-curve algebra. -/
theorem ofOverlap_mul
    (z w : Overlap) :
    ofOverlap (N13FormalLineBundleCech.mulOverlap z w) =
      ofOverlap z * ofOverlap w := by
  have hv :
      vClass ^ 2 =
        algebraMap Laurent FormalCurve
            (N13FormalLineBundleCech.rhsInfinity (R := R₂)) -
          algebraMap Laurent FormalCurve
              (N13FormalLineBundleCech.hInfinity (R := R₂)) *
            vClass := by
    linear_combination vClass_relation
  change
    algebraMap Laurent FormalCurve
          (z.1 * w.1 +
            z.2 * w.2 *
              N13FormalLineBundleCech.rhsInfinity (R := R₂)) +
        algebraMap Laurent FormalCurve
            (z.1 * w.2 + z.2 * w.1 -
              z.2 * w.2 *
                N13FormalLineBundleCech.hInfinity (R := R₂)) *
          vClass =
      (algebraMap Laurent FormalCurve z.1 +
          algebraMap Laurent FormalCurve z.2 * vClass) *
        (algebraMap Laurent FormalCurve w.1 +
          algebraMap Laurent FormalCurve w.2 * vClass)
  simp only [map_add, map_sub, map_mul]
  linear_combination
    -(algebraMap Laurent FormalCurve z.2 *
      algebraMap Laurent FormalCurve w.2) * hv

/-- Multiplication of normal-form coordinates agrees with the pair
multiplication used by the Čech complex. -/
theorem toOverlap_mul
    (z w : FormalCurve) :
    toOverlap (z * w) =
      N13FormalLineBundleCech.mulOverlap
        (toOverlap z) (toOverlap w) := by
  apply ofOverlap_injective
  rw [ofOverlap_mul, ofOverlap_toOverlap,
    ofOverlap_toOverlap, ofOverlap_toOverlap]

@[simp] theorem toOverlap_one :
    toOverlap (1 : FormalCurve) =
      N13FormalLineBundleCech.oneOverlap (R := R₂) := by
  apply ofOverlap_injective
  rw [ofOverlap_toOverlap, ofOverlap_oneOverlap]

/-- A genuine unit on the formal overlap, whose reduction is one, supplies
the complete near-identity transition package.  Its inverse is inherited
from the unit rather than postulated separately. -/
def transitionOfUnit
    (u : FormalCurveˣ)
    (hreduce :
      N13FormalLineBundleCech.reduceOverlap
          (toOverlap (u : FormalCurve)) =
        N13FormalLineBundleCech.oneOverlap (R := N13FormalLineBundleCech.K)) :
    N13FormalLineBundleCech.NearIdentityTransition where
  transition := toOverlap (u : FormalCurve)
  inverse := toOverlap ((u⁻¹ : FormalCurveˣ) : FormalCurve)
  mul_inverse := by
    rw [← toOverlap_mul]
    simp
  inverse_mul := by
    rw [← toOverlap_mul]
    simp
  reduce_transition := hreduce

/-! ## Restriction of the actual affine coordinate ring -/

/-- Laurent monomials in the overlap parameter. -/
def tPow (n : ℤ) : Laurent :=
  HahnSeries.single n 1

@[simp] theorem tPow_mul (m n : ℤ) :
    tPow m * tPow n = tPow (m + n) := by
  simp [tPow]

@[simp] theorem tPow_zero :
    tPow 0 = 1 := rfl

/-- Evaluate an affine polynomial at `x=t⁻¹`. -/
def polyAtTInv : R₂[X] →+* Laurent :=
  Polynomial.eval₂RingHom
    (algebraMap R₂ Laurent) (tPow (-1))

@[simp] theorem polyAtTInv_X :
    polyAtTInv X = tPow (-1) := by
  simp [polyAtTInv]

@[simp] theorem polyAtTInv_C (a : R₂) :
    polyAtTInv (C a) = algebraMap R₂ Laurent a := by
  simp [polyAtTInv]

/-- The affine coefficient `x³+x+1` becomes
`t⁻³(1+t²+t³)`. -/
theorem polyAtTInv_hPoly :
    polyAtTInv
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      tPow (-3) *
        N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp only [N13GeneralizedMumfordIntegral.hPoly,
    map_add, map_pow, map_one, polyAtTInv_X]
  change
    tPow (-1) ^ 3 + tPow (-1) + 1 =
      tPow (-3) *
        (tPow 0 + tPow 2 + tPow 3)
  simp only [pow_succ, tPow_mul, mul_add, mul_one,
    tPow_zero]
  norm_num

/-- The affine right-hand side `x⁵+x⁴` becomes
`t⁻⁶(t+t²)`. -/
theorem polyAtTInv_rhsPoly :
    polyAtTInv
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      tPow (-6) *
        N13FormalLineBundleCech.rhsInfinity (R := R₂) := by
  simp only [N13GeneralizedMumfordIntegral.rhsPoly,
    map_add, map_pow, polyAtTInv_X]
  change
    tPow (-1) ^ 5 + tPow (-1) ^ 4 =
      tPow (-6) * (tPow 1 + tPow 2)
  simp only [pow_succ, tPow_mul, mul_add]
  norm_num

/-- Coefficients of the affine quadratic equation restricted to the formal
overlap. -/
def affineCoeffMap : R₂[X] →+* FormalCurve :=
  (AdjoinRoot.of formalCurvePoly).comp polyAtTInv

/-- The affine coordinate `y` restricts to `t⁻³v`. -/
def yImage : FormalCurve :=
  algebraMap Laurent FormalCurve (tPow (-3)) * vClass

/-- The proposed image of `y` satisfies the actual affine equation after
the substitution `x=t⁻¹`. -/
theorem affineCurve_relation :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
        affineCoeffMap yImage =
      0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul]
  rw [show affineCoeffMap
          (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
        algebraMap Laurent FormalCurve
          (tPow (-3) *
            N13FormalLineBundleCech.hInfinity (R := R₂)) by
      simp [affineCoeffMap, polyAtTInv_hPoly]]
  rw [show affineCoeffMap
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
        algebraMap Laurent FormalCurve
          (tPow (-6) *
            N13FormalLineBundleCech.rhsInfinity (R := R₂)) by
      simp [affineCoeffMap, polyAtTInv_rhsPoly]]
  simp only [yImage, map_mul]
  have ht :
      algebraMap Laurent FormalCurve (tPow (-3)) ^ 2 =
        algebraMap Laurent FormalCurve (tPow (-6)) := by
    rw [← map_pow]
    congr 1
    simp [pow_two, tPow_mul]
  rw [show
      (algebraMap Laurent FormalCurve (tPow (-3)) * vClass) ^ 2 =
        algebraMap Laurent FormalCurve (tPow (-6)) *
          vClass ^ 2 by
      rw [mul_pow, ht]]
  rw [← ht]
  linear_combination
    algebraMap Laurent FormalCurve (tPow (-3)) ^ 2 *
      (sub_eq_zero.mpr vClass_relation)

/-- Restriction of the actual integral affine coordinate ring to the
punctured formal infinity chart. -/
def affineToFormalCurve :
    IntegralAffineRing →+* FormalCurve :=
  AdjoinRoot.lift affineCoeffMap yImage affineCurve_relation

@[simp] theorem affineToFormalCurve_xClass
    (p : R₂[X]) :
    affineToFormalCurve
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      algebraMap Laurent FormalCurve (polyAtTInv p) := by
  exact AdjoinRoot.lift_of affineCurve_relation

@[simp] theorem affineToFormalCurve_yClass :
    affineToFormalCurve
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      yImage := by
  exact AdjoinRoot.lift_root affineCurve_relation

@[simp] theorem toOverlap_algebraMap
    (f : Laurent) :
    toOverlap (algebraMap Laurent FormalCurve f) = (f, 0) := by
  calc
    toOverlap (algebraMap Laurent FormalCurve f) =
        toOverlap (ofOverlap (f, 0)) := by
          congr 1
          simp [ofOverlap]
    _ = (f, 0) := toOverlap_ofOverlap _

@[simp] theorem toOverlap_vClass :
    toOverlap vClass = (0, 1) := by
  calc
    toOverlap vClass =
        toOverlap (ofOverlap (0, 1)) := by
          congr 1
          simp [ofOverlap]
    _ = (0, 1) := toOverlap_ofOverlap _

@[simp] theorem toOverlap_yImage :
    toOverlap yImage = (0, tPow (-3)) := by
  rw [yImage, toOverlap_mul, toOverlap_algebraMap,
    toOverlap_vClass]
  simp [N13FormalLineBundleCech.mulOverlap]

/-- The actual affine restriction written in the same coefficient pair used
by the formal Čech complex. -/
def affineOverlap (z : IntegralAffineRing) : Overlap :=
  toOverlap (affineToFormalCurve z)

@[simp] theorem affineOverlap_zero :
    affineOverlap 0 = 0 := by
  simp [affineOverlap]

@[simp] theorem affineOverlap_one :
    affineOverlap 1 =
      N13FormalLineBundleCech.oneOverlap (R := R₂) := by
  simp [affineOverlap]

@[simp] theorem affineOverlap_add
    (z w : IntegralAffineRing) :
    affineOverlap (z + w) =
      affineOverlap z + affineOverlap w := by
  simp [affineOverlap]

@[simp] theorem affineOverlap_neg
    (z : IntegralAffineRing) :
    affineOverlap (-z) = -affineOverlap z := by
  simp [affineOverlap]

@[simp] theorem affineOverlap_sub
    (z w : IntegralAffineRing) :
    affineOverlap (z - w) =
      affineOverlap z - affineOverlap w := by
  simp [sub_eq_add_neg]

/-- Actual multiplication restricts to the quadratic pair multiplication,
not to componentwise multiplication of pairs. -/
@[simp] theorem affineOverlap_mul
    (z w : IntegralAffineRing) :
    affineOverlap (z * w) =
      N13FormalLineBundleCech.mulOverlap
        (affineOverlap z) (affineOverlap w) := by
  simp [affineOverlap, toOverlap_mul]

@[simp] theorem affineOverlap_xClass
    (p : R₂[X]) :
    affineOverlap
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      (polyAtTInv p, 0) := by
  rw [affineOverlap, affineToFormalCurve_xClass]
  exact toOverlap_algebraMap _

@[simp] theorem affineOverlap_yClass :
    affineOverlap
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      (0, tPow (-3)) := by
  simp [affineOverlap]

@[simp] theorem affineOverlap_ySubClass
    (p : R₂[X]) :
    affineOverlap
      (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) p) =
      (-polyAtTInv p, tPow (-3)) := by
  rw [N13GeneralizedMumfordIntegral.ySubClass,
    affineOverlap_sub, affineOverlap_yClass,
    affineOverlap_xClass]
  ext <;> simp

/-- Every affine function has the expected Laurent normal form: a polynomial
in `t⁻¹` in the scalar component and `t⁻³` times such a polynomial in the
`v` component. -/
theorem affineOverlap_eq_coeff
    (z : IntegralAffineRing) :
    affineOverlap z =
      (polyAtTInv
          (N13GeneralizedMumfordIntegral.coeff0 z),
        polyAtTInv
            (N13GeneralizedMumfordIntegral.coeffY z) *
          tPow (-3)) := by
  calc
    affineOverlap z =
        affineOverlap
          (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) := by
          exact congrArg affineOverlap
            (N13GeneralizedMumfordIntegral.recompose z).symm
    _ =
        (polyAtTInv
            (N13GeneralizedMumfordIntegral.coeff0 z),
          polyAtTInv
              (N13GeneralizedMumfordIntegral.coeffY z) *
            tPow (-3)) := by
          simp [N13FormalLineBundleCech.mulOverlap]

/-- A polynomial in `t⁻¹` has no positive Laurent coefficients. -/
theorem polyAtTInv_coeff_of_pos
    (p : R₂[X]) (n : ℤ) (hn : 0 < n) :
    (polyAtTInv p).coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial k a =>
      change
        (Polynomial.eval₂
            (algebraMap R₂ Laurent) (tPow (-1))
            (monomial k a)).coeff n =
          0
      rw [Polynomial.eval₂_monomial]
      change
        (algebraMap R₂ Laurent a *
            HahnSeries.single (-1) 1 ^ k).coeff n =
          0
      rw [HahnSeries.single_pow]
      rw [HahnSeries.algebraMap_apply']
      simp only [PowerSeries.algebraMap_apply,
        HahnSeries.ofPowerSeries_C]
      change
        (HahnSeries.single 0 a *
            HahnSeries.single (k • (-1 : ℤ)) (1 ^ k)).coeff n =
          0
      rw [HahnSeries.single_mul_single]
      apply HahnSeries.coeff_single_of_ne
      intro hnk
      have hk : k • (-1 : ℤ) ≤ 0 := by
        simp
      omega

/-- Multiplication by `t⁻³` shifts the affine upper bound from zero to
minus three. -/
theorem polyAtTInv_mul_tPow_coeff_of_gt_negThree
    (p : R₂[X]) (n : ℤ) (hn : -3 < n) :
    (polyAtTInv p * tPow (-3)).coeff n = 0 := by
  rw [tPow, HahnSeries.coeff_mul_single]
  simp only [mul_one]
  apply polyAtTInv_coeff_of_pos
  omega

/-- The restriction of every actual affine coordinate-ring function lands
in the affine-section submodule used by the formal Čech quotient. -/
theorem affineOverlap_mem_affineSections
    (z : IntegralAffineRing) :
    affineOverlap z ∈
      N13CechLaurentSeriesCore.affineSections (R := R₂) := by
  rw [affineOverlap_eq_coeff]
  constructor
  · intro n hn
    exact polyAtTInv_coeff_of_pos _ n hn
  · intro n hn
    exact polyAtTInv_mul_tPow_coeff_of_gt_negThree _ n hn

end

end MazurProof.N13FormalCurveOverlap


