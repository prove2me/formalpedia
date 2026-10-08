-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:48:32.829227+00:00
-- url     : https://prove2.me/theorems/0673a922-e1af-47bd-88a2-66fd05c3c0da
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0

set_option autoImplicit false




/-!
# Reduction of the N13 infinity chart at two

Coefficientwise reduction induces the special infinity chart

`v² + (1+t²+t³)v = t+t²`.

The induced map is onto and its kernel is exactly the vertical ideal `(2)`.
Both statements use the common rank-two normal form `a(t) + b(t)v`; no
enumeration of the special fibre is involved.
-/

open Polynomial

namespace MazurProof.N13IntegralInfinityReduction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev K : Type :=
  N13SpecialInfinityChart.K

abbrev IntegralBase : Type :=
  N13IntegralInfinityChart.Base

abbrev SpecialBase : Type :=
  K[X]

abbrev IntegralRing : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev SpecialRing : Type :=
  N13SpecialInfinityChart.CoordinateRing

/-- Coefficient reduction on the infinity-chart base. -/
def reduceBase : R₂ →+* K :=
  N13GeneralizedMumfordReduction.reduceBase

/-- Coefficientwise reduction in the parameter `t`. -/
def reducePoly : IntegralBase →+* SpecialBase :=
  Polynomial.mapRingHom reduceBase

@[simp] theorem reducePoly_apply (p : IntegralBase) :
    reducePoly p = p.map reduceBase := rfl

@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  exact N13GeneralizedMumfordReduction.reduceBase_two

@[simp] theorem reduce_hBase :
    reducePoly N13IntegralInfinityChart.hBase =
      N13SpecialInfinityChart.hPoly := by
  simp [reducePoly, reduceBase,
    N13IntegralInfinityChart.hBase,
    N13SpecialInfinityChart.hPoly]

@[simp] theorem reduce_rhsBase :
    reducePoly N13IntegralInfinityChart.rhsBase =
      N13SpecialInfinityChart.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13IntegralInfinityChart.rhsBase,
    N13SpecialInfinityChart.rhsPoly]

theorem reduce_curvePoly :
    N13IntegralInfinityChart.infinityCurvePoly.map reducePoly =
      N13SpecialInfinityChart.curvePoly := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    N13SpecialInfinityChart.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly N13IntegralInfinityChart.hBase) * X -
        C (reducePoly N13IntegralInfinityChart.rhsBase) =
      X ^ 2 + C N13SpecialInfinityChart.hPoly * X -
        C N13SpecialInfinityChart.rhsPoly
  rw [reduce_hBase, reduce_rhsBase]

private theorem special_curve_dvd :
    N13SpecialInfinityChart.curvePoly ∣
      N13IntegralInfinityChart.infinityCurvePoly.map reducePoly := by
  rw [reduce_curvePoly]

/-- Reduction on the ordinary infinity-chart coordinate ring. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd

@[simp] theorem reduce_tClass :
    reduceCoordinate N13IntegralInfinityChart.tClass =
      N13SpecialInfinityChart.tClass := by
  simp [reduceCoordinate, N13IntegralInfinityChart.tClass,
    N13SpecialInfinityChart.tClass]

@[simp] theorem reduce_vClass :
    reduceCoordinate N13IntegralInfinityChart.vClass =
      N13SpecialInfinityChart.vClass := by
  exact AdjoinRoot.map_root
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd

/-- Ordinary base polynomials inside the ordinary infinity chart. -/
def integralBaseClass (p : IntegralBase) : IntegralRing :=
  algebraMap IntegralBase IntegralRing p

/-- Special base polynomials inside the special infinity chart. -/
def specialBaseClass (p : SpecialBase) : SpecialRing :=
  algebraMap SpecialBase SpecialRing p

@[simp] theorem reduce_integralBaseClass (p : IntegralBase) :
    reduceCoordinate (integralBaseClass p) =
      specialBaseClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd p

/-- The degree-less-than-two representative on the ordinary chart. -/
def integralNormalPoly :
    IntegralRing →ₗ[IntegralBase] IntegralBase[X] :=
  AdjoinRoot.modByMonicHom
    N13IntegralInfinityChart.infinityCurvePoly_monic

/-- Coefficients in the ordinary basis `1,v`. -/
def integralCoeff0 : IntegralRing →ₗ[IntegralBase] IntegralBase :=
  (Polynomial.lcoeff IntegralBase 0).comp integralNormalPoly

def integralCoeffV : IntegralRing →ₗ[IntegralBase] IntegralBase :=
  (Polynomial.lcoeff IntegralBase 1).comp integralNormalPoly

/-- The degree-less-than-two representative on the special chart. -/
def specialNormalPoly :
    SpecialRing →ₗ[SpecialBase] SpecialBase[X] :=
  AdjoinRoot.modByMonicHom
    N13SpecialInfinityChart.curvePoly_monic

/-- Coefficients in the special basis `1,v`. -/
def specialCoeff0 : SpecialRing →ₗ[SpecialBase] SpecialBase :=
  (Polynomial.lcoeff SpecialBase 0).comp specialNormalPoly

def specialCoeffV : SpecialRing →ₗ[SpecialBase] SpecialBase :=
  (Polynomial.lcoeff SpecialBase 1).comp specialNormalPoly

private theorem integral_curve_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num

private theorem special_curve_degree :
    N13SpecialInfinityChart.curvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13SpecialInfinityChart.curvePoly_monic.ne_zero,
    N13SpecialInfinityChart.curvePoly_natDegree]
  norm_num

theorem integralNormalPoly_eq (z : IntegralRing) :
    integralNormalPoly z =
      C (integralCoeff0 z) + C (integralCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13IntegralInfinityChart.infinityCurvePoly =
        C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0) +
          C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13IntegralInfinityChart.infinityCurvePoly)
        N13IntegralInfinityChart.infinityCurvePoly_monic
        (n := 2) (by rw [integral_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem specialNormalPoly_eq (z : SpecialRing) :
    specialNormalPoly z =
      C (specialCoeff0 z) + C (specialCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13SpecialInfinityChart.curvePoly =
        C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 0) +
          C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.curvePoly_monic
        (n := 2) (by rw [special_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Every ordinary element has a unique rank-two expression. -/
theorem integral_recompose (z : IntegralRing) :
    integralBaseClass (integralCoeff0 z) +
        integralBaseClass (integralCoeffV z) *
          N13IntegralInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        integralBaseClass (integralCoeff0 (AdjoinRoot.mk _ g)) +
              integralBaseClass (integralCoeffV (AdjoinRoot.mk _ g)) *
                N13IntegralInfinityChart.vClass =
            AdjoinRoot.mk _
              (C (integralCoeff0 (AdjoinRoot.mk _ g)) +
                C (integralCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [integralBaseClass,
                    N13IntegralInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (integralNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [integralNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13IntegralInfinityChart.infinityCurvePoly_monic
            (AdjoinRoot.mk _ g)

/-- Every special element has a unique rank-two expression. -/
theorem special_recompose (z : SpecialRing) :
    specialBaseClass (specialCoeff0 z) +
        specialBaseClass (specialCoeffV z) *
          N13SpecialInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        specialBaseClass (specialCoeff0 (AdjoinRoot.mk _ g)) +
              specialBaseClass (specialCoeffV (AdjoinRoot.mk _ g)) *
                N13SpecialInfinityChart.vClass =
            AdjoinRoot.mk _
              (C (specialCoeff0 (AdjoinRoot.mk _ g)) +
                C (specialCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [specialBaseClass,
                    N13SpecialInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (specialNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [specialNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13SpecialInfinityChart.curvePoly_monic
            (AdjoinRoot.mk _ g)

@[simp] theorem integralCoeff0_baseClass (p : IntegralBase) :
    integralCoeff0 (integralBaseClass p) = p := by
  change
    (C p %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [integral_curve_degree]
      norm_num)

@[simp] theorem integralCoeffV_baseClass (p : IntegralBase) :
    integralCoeffV (integralBaseClass p) = 0 := by
  change
    (C p %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [integral_curve_degree]
      norm_num)

@[simp] theorem integralCoeff0_vClass :
    integralCoeff0 N13IntegralInfinityChart.vClass = 0 := by
  change
    (X %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · rw [degree_X, integral_curve_degree]
    norm_num

@[simp] theorem integralCoeffV_vClass :
    integralCoeffV N13IntegralInfinityChart.vClass = 1 := by
  change
    (X %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · rw [degree_X, integral_curve_degree]
    norm_num

@[simp] theorem integralCoeff0_baseClass_mul_vClass
    (p : IntegralBase) :
    integralCoeff0
        (integralBaseClass p *
          N13IntegralInfinityChart.vClass) = 0 := by
  change integralCoeff0
    ((algebraMap IntegralBase IntegralRing p) *
      N13IntegralInfinityChart.vClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem integralCoeffV_baseClass_mul_vClass
    (p : IntegralBase) :
    integralCoeffV
        (integralBaseClass p *
          N13IntegralInfinityChart.vClass) = p := by
  change integralCoeffV
    ((algebraMap IntegralBase IntegralRing p) *
      N13IntegralInfinityChart.vClass) = p
  rw [← Algebra.smul_def]
  simp

@[simp] theorem specialCoeff0_baseClass (p : SpecialBase) :
    specialCoeff0 (specialBaseClass p) = p := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)

@[simp] theorem specialCoeffV_baseClass (p : SpecialBase) :
    specialCoeffV (specialBaseClass p) = 0 := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)

@[simp] theorem specialCoeff0_vClass :
    specialCoeff0 N13SpecialInfinityChart.vClass = 0 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num

@[simp] theorem specialCoeffV_vClass :
    specialCoeffV N13SpecialInfinityChart.vClass = 1 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num

@[simp] theorem specialCoeff0_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeff0
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = 0 := by
  change specialCoeff0
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem specialCoeffV_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeffV
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = p := by
  change specialCoeffV
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Reduction is coefficientwise in the rank-two bases. -/
@[simp] theorem reduce_integralCoeff0 (z : IntegralRing) :
    specialCoeff0 (reduceCoordinate z) =
      reducePoly (integralCoeff0 z) := by
  calc
    specialCoeff0 (reduceCoordinate z) =
        specialCoeff0
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeff0 z) := by
      simp

@[simp] theorem reduce_integralCoeffV (z : IntegralRing) :
    specialCoeffV (reduceCoordinate z) =
      reducePoly (integralCoeffV z) := by
  calc
    specialCoeffV (reduceCoordinate z) =
        specialCoeffV
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeffV z) := by
      simp

/-- Coefficientwise reduction on the base polynomial ring is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)

/-- The ordinary infinity chart reduces onto its special fibre. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective (specialCoeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective (specialCoeffV z)
  refine ⟨
    integralBaseClass p +
      integralBaseClass q * N13IntegralInfinityChart.vClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_integralBaseClass,
    reduce_vClass, hp, hq]
  exact special_recompose z

private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : IntegralBase) (hp : reducePoly p = 0) :
    ∃ q : IntegralBase, p = C (2 : R₂) * q := by
  have hmem : p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Reduction has exactly the vertical principal ideal `(2)` as kernel. -/
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
        reducePoly (integralCoeff0 z) = 0 := by
      rw [← reduce_integralCoeff0 z, hz0]
      simp
    have hV :
        reducePoly (integralCoeffV z) = 0 := by
      rw [← reduce_integralCoeffV z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hV
    rw [Ideal.mem_span_singleton]
    refine ⟨
      integralBaseClass p +
        integralBaseClass q * N13IntegralInfinityChart.vClass,
      ?_⟩
    rw [← integral_recompose z, hp, hq]
    calc
      integralBaseClass (C 2 * p) +
            integralBaseClass (C 2 * q) *
              N13IntegralInfinityChart.vClass =
          integralBaseClass (C 2) *
            (integralBaseClass p +
                integralBaseClass q *
                  N13IntegralInfinityChart.vClass) := by
            simp only [integralBaseClass, map_mul, mul_add]
            ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
            (integralBaseClass p +
              integralBaseClass q *
                N13IntegralInfinityChart.vClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate (integralBaseClass (C (2 : R₂))) = 0
    rw [reduce_integralBaseClass]
    simp [reducePoly, specialBaseClass]

end

end MazurProof.N13IntegralInfinityReduction


