-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAffineRestrictionCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAffineRestrictionCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:54:52.440966+00:00
-- url     : https://prove2.me/theorems/b4cc19b3-2f12-4ad2-a6ad-1e26f4478262
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicInfinityCompatibility_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0

set_option autoImplicit false




/-!
# Base-change compatibility of the N13 affine restriction

There are two ways to restrict an integral affine function to the two
rational branches at infinity:

1. restrict it to the integral punctured formal chart, split the two Hensel
   branches, and extend coefficients from `ℤ₂` to `ℚ₂`;
2. pass to the good generic fibre, complete the square to the sextic model,
   and use the positive and negative rational Laurent expansions.

This file proves that the resulting square commutes.  The proof checks the
two genuine affine generators `x` and `y`, with polynomial naturality
handling all functions of `x`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicInfinityCompatibility.R₂

abbrev Q₂ : Type :=
  N13TwoAdicInfinityCompatibility.Q₂

abbrev IntegralLaurent : Type :=
  N13TwoAdicInfinityCompatibility.IntegralLaurent

abbrev RationalLaurent : Type :=
  N13TwoAdicInfinityCompatibility.RationalLaurent

abbrev IntegralRing : Type :=
  N13TwoAdicCoordinateBaseChange.IntegralRing

abbrev RationalBranchPair : Type :=
  RationalLaurent × RationalLaurent

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicInfinityCompatibility.coeffMap

def laurentMap : IntegralLaurent →+* RationalLaurent :=
  N13TwoAdicInfinityCompatibility.laurentMap

def tPowQ : ℤ → RationalLaurent :=
  N13TwoAdicInfinityCompatibility.tPowQ

@[simp] theorem laurentMap_tPow
    (n : ℤ) :
    laurentMap (N13FormalCurveOverlap.tPow n) =
      tPowQ n :=
  N13TwoAdicInfinityCompatibility.laurentMap_tPow n

@[simp] theorem laurentMap_branchZero :
    laurentMap N13FormalOverlapSplit.branchZeroLaurent =
      N13TwoAdicInfinityCompatibility.rationalBranchZero :=
  N13TwoAdicInfinityCompatibility.laurentMap_branchZero

@[simp] theorem laurentMap_branchOne :
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
      N13TwoAdicInfinityCompatibility.rationalBranchOne :=
  N13TwoAdicInfinityCompatibility.laurentMap_branchOne

@[simp] theorem laurentMap_algebraMap
    (a : R₂) :
    laurentMap (algebraMap R₂ IntegralLaurent a) =
      algebraMap Q₂ RationalLaurent (coeffMap a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  change
    ((HahnSeries.single (0 : ℤ) a).map coeffMap :
        RationalLaurent) =
      HahnSeries.single (0 : ℤ) (coeffMap a)
  exact HahnSeries.map_single coeffMap.toZeroHom

@[simp] theorem tPowQ_neg_one :
    tPowQ (-1) =
      (N13Infinity.parameter Q₂)⁻¹ := by
  simp [tPowQ, N13TwoAdicInfinityCompatibility.tPowQ,
    N13Infinity.parameter, HahnSeries.inv_single]

@[simp] theorem tPowQ_neg_three :
    tPowQ (-3) =
      (N13Infinity.parameter Q₂)⁻¹ ^ 3 := by
  simp [tPowQ, N13TwoAdicInfinityCompatibility.tPowQ,
    N13Infinity.parameter, HahnSeries.inv_single,
    HahnSeries.single_pow]

/-- Coefficient extension commutes with evaluating an integral polynomial
at `t⁻¹`. -/
theorem laurentMap_polyAtTInv
    (p : R₂[X]) :
    laurentMap
        (N13FormalCurveOverlap.polyAtTInv p) =
      (p.map coeffMap).eval₂
        (algebraMap Q₂ RationalLaurent)
        ((N13Infinity.parameter Q₂)⁻¹) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | monomial n a =>
      change
        laurentMap
            ((monomial n a).eval₂
              (algebraMap R₂ IntegralLaurent)
              (N13FormalCurveOverlap.tPow (-1))) =
          ((monomial n a).map coeffMap).eval₂
            (algebraMap Q₂ RationalLaurent)
            ((N13Infinity.parameter Q₂)⁻¹)
      rw [Polynomial.eval₂_monomial,
        Polynomial.map_monomial,
        Polynomial.eval₂_monomial]
      rw [map_mul, map_pow, laurentMap_algebraMap,
        laurentMap_tPow,
        tPowQ_neg_one]

theorem rational_hPoly_at_infinity :
    (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)).eval₂
        (algebraMap Q₂ RationalLaurent)
        ((N13Infinity.parameter Q₂)⁻¹) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.hInfinityQ := by
  have h := congrArg laurentMap
    N13FormalCurveOverlap.polyAtTInv_hPoly
  rw [laurentMap_polyAtTInv] at h
  simp only [map_mul] at h
  change
    (N13TwoAdicCoordinateBaseChange.mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂))).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹) =
      laurentMap (N13FormalCurveOverlap.tPow (-3)) *
        laurentMap
          (N13FormalLineBundleCech.hInfinity (R := R₂)) at h
  rw [N13TwoAdicCoordinateBaseChange.mapPoly_hPoly] at h
  simpa [laurentMap, tPowQ] using h

theorem rational_rhsPoly_at_infinity :
    (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂)).eval₂
        (algebraMap Q₂ RationalLaurent)
        ((N13Infinity.parameter Q₂)⁻¹) =
      tPowQ (-6) *
        N13TwoAdicInfinityCompatibility.rhsInfinityQ := by
  have h := congrArg laurentMap
    N13FormalCurveOverlap.polyAtTInv_rhsPoly
  rw [laurentMap_polyAtTInv] at h
  simp only [map_mul] at h
  change
    (N13TwoAdicCoordinateBaseChange.mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹) =
      laurentMap (N13FormalCurveOverlap.tPow (-6)) *
        laurentMap
          (N13FormalLineBundleCech.rhsInfinity (R := R₂)) at h
  rw [N13TwoAdicCoordinateBaseChange.mapPoly_rhsPoly] at h
  simpa [laurentMap, tPowQ] using h

theorem ySeries_eq_tPowQ_negThree_mul_wSeries :
    N13Infinity.ySeries Q₂ =
      tPowQ (-3) * N13Infinity.wSeries Q₂ := by
  rw [N13Infinity.ySeries, tPowQ_neg_three]

theorem ySeriesMinus_eq_tPowQ_negThree_mul_neg_wSeries :
    N13InfinityMinus.ySeriesMinus Q₂ =
      tPowQ (-3) * -N13Infinity.wSeries Q₂ := by
  rw [N13InfinityMinus.ySeriesMinus_eq_neg,
    ySeries_eq_tPowQ_negThree_mul_wSeries]
  ring

theorem rationalBranchOne_eq_neg_wSeries :
    N13TwoAdicInfinityCompatibility.rationalBranchOne =
      algebraMap Q₂ RationalLaurent (1 / 2) *
        (-N13Infinity.wSeries Q₂ -
          N13TwoAdicInfinityCompatibility.hInfinityQ) := by
  rw [
    N13TwoAdicInfinityCompatibility.rationalBranchOne_eq_negative,
    N13TwoAdicInfinityCompatibility.tPowQ_three_mul_ySeriesMinus]

/-- Restriction of the good `y` coordinate to the positive rational branch. -/
theorem coordinateToLaurent_goodYInSextic :
    N13Infinity.coordinateToLaurent Q₂
        (N13GoodSexticCoordinateEquiv.goodYInSextic
          (K := Q₂)) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.rationalBranchZero := by
  simp only [N13GoodSexticCoordinateEquiv.goodYInSextic,
    Algebra.smul_def, map_mul, map_sub,
    N13GoodSexticCoordinateEquiv.sexticXHom_apply,
    N13Infinity.coordinateToLaurent_scalar,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13Infinity.coordinateToLaurent_xClass]
  rw [rational_hPoly_at_infinity,
    ySeries_eq_tPowQ_negThree_mul_wSeries]
  unfold N13TwoAdicInfinityCompatibility.rationalBranchZero
  ring

/-- Restriction of the good `y` coordinate to the negative rational branch. -/
theorem coordinateToLaurentMinus_goodYInSextic :
    N13InfinityMinus.coordinateToLaurentMinus Q₂
        (N13GoodSexticCoordinateEquiv.goodYInSextic
          (K := Q₂)) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.rationalBranchOne := by
  simp only [N13GoodSexticCoordinateEquiv.goodYInSextic,
    Algebra.smul_def, map_mul, map_sub,
    N13GoodSexticCoordinateEquiv.sexticXHom_apply,
    N13InfinityMinus.coordinateToLaurentMinus_scalar,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass]
  rw [rational_hPoly_at_infinity,
    ySeriesMinus_eq_tPowQ_negThree_mul_neg_wSeries,
    rationalBranchOne_eq_neg_wSeries]
  ring

abbrev IntegralBranchPair : Type :=
  IntegralLaurent × IntegralLaurent

/-- Restrict to the integral formal overlap and evaluate on its two Hensel
branches. -/
def integralFormalBranches :
    IntegralRing →+* IntegralBranchPair :=
  N13FormalOverlapSplit.formalBranchEval.comp
    N13FormalCurveOverlap.affineToFormalCurve

/-- Extend both integral Laurent branches coefficientwise to `ℚ₂`. -/
def laurentPairMap :
    IntegralBranchPair →+* RationalBranchPair :=
  ((laurentMap).comp
      (RingHom.fst IntegralLaurent IntegralLaurent)).prod
    ((laurentMap).comp
      (RingHom.snd IntegralLaurent IntegralLaurent))

@[simp] theorem laurentPairMap_apply
    (z : IntegralBranchPair) :
    laurentPairMap z =
      (laurentMap z.1, laurentMap z.2) :=
  rfl

/-- The integral-formal route around the restriction square. -/
def integralViaFormalBranches :
    IntegralRing →+* RationalBranchPair :=
  laurentPairMap.comp integralFormalBranches

/-- The rational-sextic route around the restriction square. -/
def integralViaRationalBranches :
    IntegralRing →+* RationalBranchPair :=
  (N13TwoInfinityRestriction.coordinateToBranches Q₂).comp
    N13TwoAdicCoordinateBaseChange.integralToSextic

@[simp] theorem integralFormalBranches_xClass
    (p : R₂[X]) :
    integralFormalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      (N13FormalCurveOverlap.polyAtTInv p,
        N13FormalCurveOverlap.polyAtTInv p) := by
  simp [integralFormalBranches,
    N13FormalOverlapSplit.formalBranchEval]

@[simp] theorem integralFormalBranches_yClass :
    integralFormalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (N13FormalCurveOverlap.tPow (-3) *
          N13FormalOverlapSplit.branchZeroLaurent,
        N13FormalCurveOverlap.tPow (-3) *
          N13FormalOverlapSplit.branchOneLaurent) := by
  simp [integralFormalBranches,
    N13FormalOverlapSplit.formalBranchEval,
    N13FormalCurveOverlap.yImage]

@[simp] theorem integralViaFormalBranches_xClass
    (p : R₂[X]) :
    integralViaFormalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      ((p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹),
        (p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹)) := by
  simp [integralViaFormalBranches,
    laurentMap_polyAtTInv]

@[simp] theorem integralViaFormalBranches_yClass :
    integralViaFormalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchZero,
        tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchOne) := by
  simp [integralViaFormalBranches, map_mul,
    laurentMap_branchZero, laurentMap_branchOne]

@[simp] theorem integralViaRationalBranches_xClass
    (p : R₂[X]) :
    integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      ((p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹),
        (p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹)) := by
  simp [integralViaRationalBranches,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    N13TwoInfinityRestriction.coordinateToBranches,
    N13TwoAdicCoordinateBaseChange.mapPoly, coeffMap]
  rfl

@[simp] theorem integralViaRationalBranches_yClass :
    integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchZero,
        tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchOne) := by
  simp [integralViaRationalBranches,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    N13TwoInfinityRestriction.coordinateToBranches,
    coordinateToLaurent_goodYInSextic,
    coordinateToLaurentMinus_goodYInSextic]

/-- Pointwise commutativity of the affine restriction/base-change square. -/
theorem affineRestriction_commutes
    (z : IntegralRing) :
    integralViaFormalBranches z =
      integralViaRationalBranches z := by
  calc
    integralViaFormalBranches z =
        integralViaFormalBranches
          (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) := by
          exact congrArg integralViaFormalBranches
            (N13GeneralizedMumfordIntegral.recompose z).symm
    _ =
        integralViaRationalBranches
          (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp
    _ = integralViaRationalBranches z := by
      exact congrArg integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.recompose z)

/-- The full affine restriction square commutes as an equality of ring
homomorphisms. -/
theorem affineRestriction_square :
    integralViaFormalBranches =
      integralViaRationalBranches := by
  apply RingHom.ext_iff.mpr
  exact affineRestriction_commutes

end

end MazurProof.N13TwoAdicAffineRestrictionCompatibility


