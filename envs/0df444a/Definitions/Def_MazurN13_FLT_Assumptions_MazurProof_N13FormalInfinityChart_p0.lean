-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:42:33.288312+00:00
-- url     : https://prove2.me/theorems/3dc3e0ff-1b7d-405c-be8d-cbadb4e58926
-- title:
--   FLT.Assumptions.MazurProof.N13FormalInfinityChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FormalInfinityChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FormalInfinityChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalCurveOverlap_p0

set_option autoImplicit false




/-!
# The actual formal infinity chart of the N13 integral curve

The additive Čech calculation described the infinity-chart image as pairs of
power series.  This file realizes that submodule as the image of the actual
quadratic formal curve

`ℤ₂[[t]][v] / (v² + (1+t²+t³)v - (t+t²))`

inside the punctured formal overlap.  In particular, the previously defined
`infinitySections` is neither an approximation nor a coefficientwise
superset: it is exactly the restriction image of the genuine chart ring.
-/

open Polynomial

namespace MazurProof.N13FormalInfinityChart

noncomputable section

open HahnSeries
open scoped PowerSeries LaurentSeries

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalCurveOverlap.R₂

abbrev Power : Type :=
  PowerSeries R₂

abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent

abbrev Overlap : Type :=
  N13FormalCurveOverlap.Overlap

abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve

/-- The coefficient of `v` in the formal infinity equation. -/
def hPower : Power :=
  1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3

/-- The right-hand side of the formal infinity equation. -/
def rhsPower : Power :=
  PowerSeries.X + PowerSeries.X ^ 2

/-- The quadratic equation on the complete infinity chart. -/
def infinityCurvePoly : Power[X] :=
  X ^ 2 + Polynomial.C hPower * X -
    Polynomial.C rhsPower

theorem infinityCurvePoly_monic :
    infinityCurvePoly.Monic := by
  unfold infinityCurvePoly
  monicity <;> norm_num

theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num

private theorem infinityCurvePoly_degree :
    infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree infinityCurvePoly_monic.ne_zero,
    infinityCurvePoly_natDegree]
  norm_num

/-- The actual complete formal infinity-chart ring. -/
abbrev InfinityCurve : Type :=
  AdjoinRoot infinityCurvePoly

/-- Its formal coordinate `v`. -/
def vClass : InfinityCurve :=
  AdjoinRoot.root infinityCurvePoly

/-- Coercion of power series to Laurent series as a ring homomorphism. -/
def includePowerRing : Power →+* Laurent :=
  HahnSeries.ofPowerSeries ℤ R₂

@[simp] theorem includePowerRing_X :
    includePowerRing PowerSeries.X =
      N13FormalCurveOverlap.tPow 1 := by
  exact HahnSeries.ofPowerSeries_X

@[simp] theorem includePowerRing_hPower :
    includePowerRing hPower =
      N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp [includePowerRing, hPower,
    N13FormalLineBundleCech.hInfinity,
    N13FormalLineBundleCech.tPow]

@[simp] theorem includePowerRing_rhsPower :
    includePowerRing rhsPower =
      N13FormalLineBundleCech.rhsInfinity (R := R₂) := by
  simp [includePowerRing, rhsPower,
    N13FormalLineBundleCech.rhsInfinity,
    N13FormalLineBundleCech.tPow]

/-- Restriction of formal-chart coefficients to the punctured overlap. -/
def infinityCoeffMap : Power →+* FormalCurve :=
  (AdjoinRoot.of N13FormalCurveOverlap.formalCurvePoly).comp
    includePowerRing

/-- The overlap coordinate `v` satisfies the complete-chart equation. -/
theorem infinityCurve_relation :
    infinityCurvePoly.eval₂
        infinityCoeffMap N13FormalCurveOverlap.vClass =
      0 := by
  simp only [infinityCurvePoly, Polynomial.eval₂_sub,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_mul]
  change
    N13FormalCurveOverlap.vClass ^ 2 +
          algebraMap Laurent FormalCurve
              (includePowerRing hPower) *
            N13FormalCurveOverlap.vClass -
        algebraMap Laurent FormalCurve
          (includePowerRing rhsPower) =
      0
  rw [includePowerRing_hPower, includePowerRing_rhsPower]
  exact sub_eq_zero.mpr N13FormalCurveOverlap.vClass_relation

/-- Restriction from the complete formal chart to its punctured overlap. -/
def infinityToFormalCurve :
    InfinityCurve →+* FormalCurve :=
  AdjoinRoot.lift infinityCoeffMap
    N13FormalCurveOverlap.vClass infinityCurve_relation

@[simp] theorem infinityToFormalCurve_of
    (f : Power) :
    infinityToFormalCurve
        (algebraMap Power InfinityCurve f) =
      algebraMap Laurent FormalCurve
        (includePowerRing f) := by
  exact AdjoinRoot.lift_of infinityCurve_relation

@[simp] theorem infinityToFormalCurve_vClass :
    infinityToFormalCurve vClass =
      N13FormalCurveOverlap.vClass := by
  exact AdjoinRoot.lift_root infinityCurve_relation

/-! ## Normal form on the complete chart -/

def normalPoly :
    InfinityCurve →ₗ[Power] Power[X] :=
  AdjoinRoot.modByMonicHom infinityCurvePoly_monic

def coeff0 :
    InfinityCurve →ₗ[Power] Power :=
  (Polynomial.lcoeff Power 0).comp normalPoly

def coeffV :
    InfinityCurve →ₗ[Power] Power :=
  (Polynomial.lcoeff Power 1).comp normalPoly

theorem normalPoly_eq_C_add_C_mul_X
    (z : InfinityCurve) :
    normalPoly z =
      C (coeff0 z) + C (coeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change
        g %ₘ infinityCurvePoly =
          C ((g %ₘ infinityCurvePoly).coeff 0) +
            C ((g %ₘ infinityCurvePoly).coeff 1) * X
      have hsum :=
        Polynomial.sum_modByMonic_coeff
          (p := g) (q := infinityCurvePoly)
          infinityCurvePoly_monic (n := 2)
          (by rw [infinityCurvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Every complete-chart function has a unique pair of power-series
coefficients in the basis `1,v`. -/
theorem recompose
    (z : InfinityCurve) :
    algebraMap Power InfinityCurve (coeff0 z) +
        algebraMap Power InfinityCurve (coeffV z) * vClass =
      z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        algebraMap Power InfinityCurve
              (coeff0 (AdjoinRoot.mk infinityCurvePoly g)) +
            algebraMap Power InfinityCurve
                (coeffV (AdjoinRoot.mk infinityCurvePoly g)) *
              vClass =
            AdjoinRoot.mk infinityCurvePoly
              (C (coeff0 (AdjoinRoot.mk infinityCurvePoly g)) +
                C (coeffV (AdjoinRoot.mk infinityCurvePoly g)) * X) := by
                  simp [vClass, AdjoinRoot.algebraMap_eq]
        _ =
            AdjoinRoot.mk infinityCurvePoly
              (normalPoly (AdjoinRoot.mk infinityCurvePoly g)) := by
                  rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk infinityCurvePoly g :=
          AdjoinRoot.mk_leftInverse infinityCurvePoly_monic _

/-- A power-series coefficient pair as an actual complete-chart function. -/
def ofPowerPair (z : Power × Power) : InfinityCurve :=
  algebraMap Power InfinityCurve z.1 +
    algebraMap Power InfinityCurve z.2 * vClass

/-- Restriction to the coefficient pair used by the formal Čech complex. -/
def infinityOverlap (z : InfinityCurve) : Overlap :=
  N13FormalCurveOverlap.toOverlap
    (infinityToFormalCurve z)

theorem infinityOverlap_eq_coeff
    (z : InfinityCurve) :
    infinityOverlap z =
      N13CechLaurentSeriesCore.includePowerPair
        (coeff0 z, coeffV z) := by
  calc
    infinityOverlap z =
        infinityOverlap
          (algebraMap Power InfinityCurve (coeff0 z) +
            algebraMap Power InfinityCurve (coeffV z) * vClass) := by
          exact congrArg infinityOverlap (recompose z).symm
    _ =
        N13CechLaurentSeriesCore.includePowerPair
          (coeff0 z, coeffV z) := by
          simp only [infinityOverlap, map_add, map_mul,
            infinityToFormalCurve_of,
            infinityToFormalCurve_vClass]
          rw [N13FormalCurveOverlap.toOverlap_mul,
            N13FormalCurveOverlap.toOverlap_algebraMap,
            N13FormalCurveOverlap.toOverlap_algebraMap,
            N13FormalCurveOverlap.toOverlap_vClass]
          apply Prod.ext <;>
            simp [N13FormalLineBundleCech.mulOverlap,
              N13CechLaurentSeriesCore.includePowerPair,
              N13CechLaurentSeriesCore.includePower,
              includePowerRing]

theorem infinityOverlap_ofPowerPair
    (z : Power × Power) :
    infinityOverlap (ofPowerPair z) =
      N13CechLaurentSeriesCore.includePowerPair z := by
  simp only [infinityOverlap, ofPowerPair, map_add, map_mul,
    infinityToFormalCurve_of, infinityToFormalCurve_vClass]
  rw [N13FormalCurveOverlap.toOverlap_mul,
    N13FormalCurveOverlap.toOverlap_algebraMap,
    N13FormalCurveOverlap.toOverlap_algebraMap,
    N13FormalCurveOverlap.toOverlap_vClass]
  apply Prod.ext <;>
    simp [N13FormalLineBundleCech.mulOverlap,
      N13CechLaurentSeriesCore.includePowerPair,
      N13CechLaurentSeriesCore.includePower,
      includePowerRing]

/-- Every actual complete-chart function restricts to an infinity section. -/
theorem infinityOverlap_mem_infinitySections
    (z : InfinityCurve) :
    infinityOverlap z ∈
      N13CechLaurentSeriesCore.infinitySections (R := R₂) := by
  rw [infinityOverlap_eq_coeff,
    N13CechLaurentSeriesCore.infinitySections_eq_range]
  exact
    ⟨(coeff0 z, coeffV z), rfl⟩

/-- Conversely every pair satisfying the infinity-section coefficient
condition comes from an actual function on the complete formal chart. -/
theorem exists_infinity_preimage
    (z : Overlap)
    (hz :
      z ∈ N13CechLaurentSeriesCore.infinitySections (R := R₂)) :
    ∃ w : InfinityCurve, infinityOverlap w = z := by
  rw [N13CechLaurentSeriesCore.infinitySections_eq_range] at hz
  obtain ⟨f, rfl⟩ := hz
  exact ⟨ofPowerPair f, infinityOverlap_ofPowerPair f⟩

/-- The actual formal infinity chart has exactly the restriction image used
in the Čech quotient. -/
theorem range_infinityOverlap :
    Set.range infinityOverlap =
      N13CechLaurentSeriesCore.infinitySections (R := R₂) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact infinityOverlap_mem_infinitySections w
  · intro hz
    exact exists_infinity_preimage z hz

end

end MazurProof.N13FormalInfinityChart


