-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveChartTransport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveChartTransport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:28:34.62605+00:00
-- url     : https://prove2.me/theorems/f73c5a2e-e48a-4103-b10e-60efcd8c0774
-- title:
--   FLT.Assumptions.MazurProof.N13PrimitiveChartTransport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13PrimitiveChartTransport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13PrimitiveChartTransport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChartComparison_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCurveProperties_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Transport an affine numerator and denominator with nonzero reductions to
the ordinary infinity chart without losing their reductions. Both chart
fractions are proved equal by an exact overlap cross-product equation.
No equality of line ideals is assumed or claimed in this transport lemma.
-/

namespace MazurProof.N13PrimitiveChartTransport

noncomputable section
open Polynomial
open scoped nonZeroDivisors

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev A := N13OrdinaryCurveOverlap.AffineCurve
abbrev B := N13OrdinaryCurveOverlap.InfinityCurve
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
abbrev As := N13SpecialCurveOverlap.AffineCurve
abbrev Bs := N13SpecialCurveOverlap.CoordinateRing
abbrev Os := N13SpecialCurveOverlap.InfinityOverlap
abbrev AOs := N13SpecialCurveOverlap.AffineOverlap

theorem special_x_ne_zero : N13SpecialCurveOverlap.xClass ≠ 0 :=
  N13GoodCoordinateRingTwo.xClass_ne_zero Polynomial.X_ne_zero

private instance instIsDomainAOs : IsDomain AOs :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors special_x_ne_zero)

private instance instIsDomainOs : IsDomain Os :=
  N13SpecialCurveOverlap.overlapEquiv.symm.toMulEquiv.isDomain AOs

theorem special_affineToInfinityOverlap_injective :
    Function.Injective N13SpecialCurveOverlap.affineToInfinityOverlap := by
  intro a b hab
  apply IsLocalization.injective AOs
    (powers_le_nonZeroDivisors_of_noZeroDivisors special_x_ne_zero)
  apply N13SpecialCurveOverlap.overlapEquiv.injective
  simpa only [N13SpecialCurveOverlap.overlapEquiv_apply,
    N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap] using hab

private theorem reduce_affine (a : A) :
    N13OverlapReductionCompatibility.reduceInfinityOverlap
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13SpecialCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
  DFunLike.congr_fun
    N13TwoChartSpecialRestriction.reduceInfinityOverlap_comp_affineToInfinityOverlap a

private theorem reduce_infinity (b : B) :
    N13OverlapReductionCompatibility.reduceInfinityOverlap (algebraMap B O b) =
      algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate b) :=
  DFunLike.congr_fun
    N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap b

private theorem reduced_overlap_t_isUnit :
    IsUnit (N13OverlapReductionCompatibility.reduceInfinityOverlap
      (algebraMap B O N13IntegralInfinityChart.tClass)) :=
  (IsLocalization.Away.algebraMap_isUnit N13IntegralInfinityChart.tClass :
    IsUnit (algebraMap B O N13IntegralInfinityChart.tClass)).map
      N13OverlapReductionCompatibility.reduceInfinityOverlap

theorem reduced_t_ne_zero :
    N13IntegralInfinityReduction.reduceCoordinate N13IntegralInfinityChart.tClass ≠ 0 := by
  intro ht
  apply reduced_overlap_t_isUnit.ne_zero
  rw [reduce_infinity, ht, map_zero]

/-- Clear only a power of t in a single affine function. Nonzero reduction
survives because the reduced affine restriction is injective and t is a unit
on the reduced overlap. -/
theorem exists_infinity_numerator
    (a : A) (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0) :
    ∃ n : ℕ, ∃ c : B,
      N13IntegralInfinityReduction.reduceCoordinate c ≠ 0 ∧
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ n =
        algebraMap B O c := by
  obtain ⟨⟨c, s⟩, hc⟩ := IsLocalization.surj
    (Submonoid.powers N13IntegralInfinityChart.tClass)
    (N13OrdinaryCurveOverlap.affineToInfinityOverlap a)
  obtain ⟨n, hn⟩ := s.property
  have hs : algebraMap B O (s : B) =
      (algebraMap B O N13IntegralInfinityChart.tClass) ^ n := by
    rw [← hn, map_pow]
  have hc' : N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
      (algebraMap B O N13IntegralInfinityChart.tClass) ^ n = algebraMap B O c := by
    simpa only [hs] using hc
  refine ⟨n, c, ?_, hc'⟩
  intro hc0
  have haO : N13OverlapReductionCompatibility.reduceInfinityOverlap
      (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) ≠ 0 := by
    rw [reduce_affine, ← map_zero N13SpecialCurveOverlap.affineToInfinityOverlap]
    exact special_affineToInfinityOverlap_injective.ne ha
  have htO := reduced_overlap_t_isUnit.ne_zero
  have hm := congrArg N13OverlapReductionCompatibility.reduceInfinityOverlap hc'
  have hreduce_c : N13OverlapReductionCompatibility.reduceInfinityOverlap ((algebraMap B O) c) =
      algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate c) := by
    simp [N13OverlapReductionCompatibility.reduceInfinityOverlap_algebraMap]
    rfl
  simp only [map_mul, map_pow] at hm
  rw [hreduce_c, hc0, map_zero] at hm
  exact (mul_ne_zero haO (pow_ne_zero n htO)) hm

/-- Every affine primitive fraction admits a primitive infinity-chart
presentation of exactly the same fraction on the ordinary overlap. -/
theorem exists_common_primitive_presentation
    (a b : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0) :
    ∃ c d : B,
      N13IntegralInfinityReduction.reduceCoordinate c ≠ 0 ∧
      N13IntegralInfinityReduction.reduceCoordinate d ≠ 0 ∧
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
        N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c := by
  obtain ⟨n, c, hc0, hc⟩ := exists_infinity_numerator a ha
  obtain ⟨m, d, hd0, hd⟩ := exists_infinity_numerator b hb
  refine ⟨N13IntegralInfinityChart.tClass ^ m * c,
    N13IntegralInfinityChart.tClass ^ n * d, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero m reduced_t_ne_zero) hc0
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n reduced_t_ne_zero) hd0
  · rw [map_mul, map_mul, map_pow, map_pow]
    calc
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          ((algebraMap B O N13IntegralInfinityChart.tClass) ^ n * algebraMap B O d) =
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ n) * algebraMap B O d := by ring
      _ = algebraMap B O c * algebraMap B O d := by rw [hc]
      _ = (N13OrdinaryCurveOverlap.affineToInfinityOverlap b *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ m) * algebraMap B O c := by
        rw [hd]
        ring
      _ = N13OrdinaryCurveOverlap.affineToInfinityOverlap b *
          ((algebraMap B O N13IntegralInfinityChart.tClass) ^ m * algebraMap B O c) := by ring

end
end MazurProof.N13PrimitiveChartTransport


