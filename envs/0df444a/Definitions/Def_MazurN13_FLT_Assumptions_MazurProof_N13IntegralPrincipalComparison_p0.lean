-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralPrincipalComparison_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralPrincipalComparison_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:18:26.44566+00:00
-- url     : https://prove2.me/theorems/9f4426ac-97d1-47eb-aba1-265ef46de313
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralPrincipalComparison source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralPrincipalComparison

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralPrincipalComparison
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveAffineComparison_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GenericInfinityComparison_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Transport the proved integral affine equation to the actual ordinary
overlap, then use the two actual branch equations to descend the infinity
equation. The final comparison uses one common primitive fraction.
-/

namespace MazurProof.N13IntegralPrincipalComparison

noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing

private theorem cross_cleared_ideals {T : Type*} [CommRing T] [IsDomain T]
    (a b c d : T) (hb : b ≠ 0) (I J : Ideal T)
    (hideal : Ideal.span ({a} : Set T) * I = Ideal.span ({b} : Set T) * J)
    (hcross : a * d = b * c) :
    Ideal.span ({c} : Set T) * I = Ideal.span ({d} : Set T) * J := by
  apply Ideal.span_singleton_mul_right_injective hb
  calc
    Ideal.span ({b} : Set T) * (Ideal.span ({c} : Set T) * I) =
        Ideal.span ({b * c} : Set T) * I := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span ({a * d} : Set T) * I := by rw [hcross]
    _ = Ideal.span ({d} : Set T) * (Ideal.span ({a} : Set T) * I) := by
      rw [← Ideal.span_singleton_mul_span_singleton]
      ac_rfl
    _ = Ideal.span ({d} : Set T) * (Ideal.span ({b} : Set T) * J) := by rw [hideal]
    _ = Ideal.span ({b} : Set T) * (Ideal.span ({d} : Set T) * J) := by ac_rfl

theorem infinity_overlap_cleared_equation
    (L M : Line) (a b : A) (c d : B) (hb : b ≠ 0)
    (haffine : Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    Ideal.map (algebraMap B O) (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map (algebraMap B O) (Ideal.span ({d} : Set B) * M.infinityIdeal) := by
  have hbO : N13OrdinaryCurveOverlap.affineToInfinityOverlap b ≠ 0 := by
    intro h
    apply hb
    apply N13IntegralFractionalHull.integralToRational_injective
    apply N13Infinity.coordinateToLaurent_injective Q₂
    simpa only [map_zero, positiveOverlap_affine] using congrArg positiveOverlap h
  have he := congrArg (Ideal.map N13OrdinaryCurveOverlap.affineToInfinityOverlap) haffine
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    L.overlap_eq, M.overlap_eq] at he
  simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using
    cross_cleared_ideals _ _ _ _ hbO _ _ he hcross

private def infinityToGenericOverlap : B →+* GenericOverlap :=
  (algebraMap GenericInfinity GenericOverlap).comp (algebraMap B GenericInfinity)

private theorem t_unit : IsUnit
    (infinityToGenericOverlap N13IntegralInfinityChart.tClass) :=
  IsLocalization.Away.algebraMap_isUnit genericT

private def ordinaryToGenericOverlap : O →+* GenericOverlap :=
  IsLocalization.Away.lift N13IntegralInfinityChart.tClass t_unit

private theorem ordinaryToGenericOverlap_comp :
    ordinaryToGenericOverlap.comp (algebraMap B O) = infinityToGenericOverlap :=
  IsLocalization.Away.lift_comp N13IntegralInfinityChart.tClass t_unit

theorem generic_away_equation_of_ordinary (I J : Ideal B)
    (h : Ideal.map (algebraMap B O) I = Ideal.map (algebraMap B O) J) :
    Ideal.map (algebraMap GenericInfinity GenericOverlap)
        (Ideal.map (algebraMap B GenericInfinity) I) =
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
        (Ideal.map (algebraMap B GenericInfinity) J) := by
  have hm := congrArg (Ideal.map ordinaryToGenericOverlap) h
  simpa only [Ideal.map_map, ordinaryToGenericOverlap_comp, infinityToGenericOverlap] using hm

theorem data_infinity_reduction_ne_bot (D : Data) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate D.charts.infinityIdeal ≠ ⊥ := by
  change (N13TwoChartSpecialRestriction.restrict D.charts).infinityIdeal ≠ ⊥
  rw [D.special_infinity]
  exact N13InvertibleReductionSaturation.special_divisor_infinityIdeal_ne_bot D.specialDivisor

private theorem principal_mul_infinity_isUnit (c : B) (hc : c ≠ 0) (L : Line) :
    IsUnit ((Ideal.span ({c} : Set B) * L.infinityIdeal : Ideal B) :
      N13IntegralInfinityPointSpread.InfinityFractionalIdeal) := by
  rw [FractionalIdeal.coeIdeal_mul]
  have hprincipal : IsUnit ((Ideal.span ({c} : Set B) : Ideal B) :
      N13IntegralInfinityPointSpread.InfinityFractionalIdeal) := by
    exact IsUnit.of_mul_eq_one _ (FractionalIdeal.coe_ideal_span_singleton_mul_inv
      N13IntegralInfinityPointSpread.FunctionField hc)
  exact hprincipal.mul L.infinity_isUnit

private theorem principal_mul_reduction_ne_bot
    (c : B) (hc : N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (I : Ideal B) (hI : Ideal.map N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate (Ideal.span ({c} : Set B) * I) ≠ ⊥ := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  intro h
  rcases Ideal.mul_eq_bot.mp h with hp | hI0
  · apply hc
    have hm := Ideal.mem_span_singleton_self (N13IntegralInfinityReduction.reduceCoordinate c)
    rwa [hp, Ideal.mem_bot] at hm
  · exact hI hI0

/-- Once the affine equation and actual branch equations have been derived,
the whole integral infinity equation follows; no generic infinity ideal
equality or approximation predicate remains as an input. -/
theorem integral_infinity_cleared_equation
    (L M : Line) (a b : A) (c d : B) (hb : b ≠ 0)
    (hc : N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (hd : N13IntegralInfinityReduction.reduceCoordinate d ≠ 0)
    (hL : Ideal.map N13IntegralInfinityReduction.reduceCoordinate L.infinityIdeal ≠ ⊥)
    (hM : Ideal.map N13IntegralInfinityReduction.reduceCoordinate M.infinityIdeal ≠ ⊥)
    (haffine : Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c)
    (hplus : Ideal.map positiveExpansion (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map positiveExpansion (Ideal.span ({d} : Set B) * M.infinityIdeal))
    (hminus : Ideal.map negativeExpansion (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map negativeExpansion (Ideal.span ({d} : Set B) * M.infinityIdeal)) :
    Ideal.span ({c} : Set B) * L.infinityIdeal = Ideal.span ({d} : Set B) * M.infinityIdeal := by
  exact integral_ideal_eq_of_overlap_and_branches _ _
    (principal_mul_infinity_isUnit c (fun h => hc (by simp [h])) L)
    (principal_mul_infinity_isUnit d (fun h => hd (by simp [h])) M)
    (principal_mul_reduction_ne_bot c hc _ hL)
    (principal_mul_reduction_ne_bot d hd _ hM) hplus hminus
    (generic_away_equation_of_ordinary _ _
      (infinity_overlap_cleared_equation L M a b c d hb haffine hcross))

end
end MazurProof.N13IntegralPrincipalComparison


