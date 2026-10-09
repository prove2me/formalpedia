-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChartComparison_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CoherentChartComparison_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:20:19.06682+00:00
-- url     : https://prove2.me/theorems/c11bf120-bc95-4c4c-bd44-6d84fb2d5c23
-- title:
--   FLT.Assumptions.MazurProof.N13CoherentChartComparison source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CoherentChartComparison

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CoherentChartComparison
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartPicardRealization_p0

set_option autoImplicit false




/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate only. Lean elaboration / build / axiom checks: NOT RUN.
A denominator-cleared, two-chart principal comparison. Existence is not asserted.
-/

namespace MazurProof.N13CoherentChartComparison

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Line := N13TwoChartPicardRealization.Line
abbrev A := N13IntegralGraphJacobian.IntegralRing
abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
abbrev As := N13TwoChartSpecialRestriction.SpecialAffine
abbrev Bs := N13TwoChartSpecialRestriction.SpecialInfinity
abbrev Os := N13SpecialCurveOverlap.InfinityOverlap

/-- Reduction preserves a denominator-cleared equality of invertible ideals.
No assertion about lifting a special rational function is made. -/
theorem map_cleared_ideal_eq
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (I J : Ideal R)
    (h : Ideal.span ({a} : Set R) * I = Ideal.span ({b} : Set R) * J) :
    Ideal.span ({f a} : Set S) * Ideal.map f I =
      Ideal.span ({f b} : Set S) * Ideal.map f J := by
  have hm := congrArg (Ideal.map f) h
  simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using hm

/-- Nonzero numerator and denominator on both special charts, with their
fractions equal on the overlap. This encodes principal equivalence, not an
assertion about the finite Abel code. -/
structure SpecialComparison
    (L M : N13TwoChartSpecialRestriction.ChartPair) where
  aNum : As
  aDen : As
  iNum : Bs
  iDen : Bs
  aNum_ne : aNum ≠ 0
  aDen_ne : aDen ≠ 0
  iNum_ne : iNum ≠ 0
  iDen_ne : iDen ≠ 0
  affine_eq :
    Ideal.span ({aNum} : Set As) * L.affineIdeal =
      Ideal.span ({aDen} : Set As) * M.affineIdeal
  infinity_eq :
    Ideal.span ({iNum} : Set Bs) * L.infinityIdeal =
      Ideal.span ({iDen} : Set Bs) * M.infinityIdeal
  overlap_eq :
    N13SpecialCurveOverlap.affineToInfinityOverlap aNum * algebraMap Bs Os iDen =
      N13SpecialCurveOverlap.affineToInfinityOverlap aDen * algebraMap Bs Os iNum

/-- One common rational principal comparison whose two chart presentations
have nonzero reduction. The nonzero-reduction requirements exclude a
vertical factor being silently discarded in specialization. -/
structure IntegralComparison (L M : Line) where
  aNum : A
  aDen : A
  iNum : B
  iDen : B
  aNum_ne : N13GeneralizedMumfordReduction.reduceCoordinate aNum ≠ 0
  aDen_ne : N13GeneralizedMumfordReduction.reduceCoordinate aDen ≠ 0
  iNum_ne : N13IntegralInfinityReduction.reduceCoordinate iNum ≠ 0
  iDen_ne : N13IntegralInfinityReduction.reduceCoordinate iDen ≠ 0
  affine_eq :
    Ideal.span ({aNum} : Set A) * L.affineIdeal =
      Ideal.span ({aDen} : Set A) * M.affineIdeal
  infinity_eq :
    Ideal.span ({iNum} : Set B) * L.infinityIdeal =
      Ideal.span ({iDen} : Set B) * M.infinityIdeal
  overlap_eq :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap aNum * algebraMap B O iDen =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap aDen * algebraMap B O iNum

/-- The reduction of an actual whole-chart principal comparison is again
such a comparison. Obtaining this input for normalized representatives is a
separate geometric theorem. -/
def IntegralComparison.reduce {L M : Line} (h : IntegralComparison L M) :
    SpecialComparison (N13TwoChartSpecialRestriction.restrict L)
      (N13TwoChartSpecialRestriction.restrict M) where
  aNum := N13GeneralizedMumfordReduction.reduceCoordinate h.aNum
  aDen := N13GeneralizedMumfordReduction.reduceCoordinate h.aDen
  iNum := N13IntegralInfinityReduction.reduceCoordinate h.iNum
  iDen := N13IntegralInfinityReduction.reduceCoordinate h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := map_cleared_ideal_eq _ _ _ _ _ h.affine_eq
  infinity_eq := map_cleared_ideal_eq _ _ _ _ _ h.infinity_eq
  overlap_eq := by
    have hm := congrArg N13OverlapReductionCompatibility.reduceInfinityOverlap h.overlap_eq
    have ha (a : A) :
        N13OverlapReductionCompatibility.reduceInfinityOverlap
            (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
          N13SpecialCurveOverlap.affineToInfinityOverlap
            (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
      DFunLike.congr_fun
        N13TwoChartSpecialRestriction.reduceInfinityOverlap_comp_affineToInfinityOverlap a
    have hi (i : B) :
        N13OverlapReductionCompatibility.reduceInfinityOverlap (algebraMap B O i) =
          algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate i) :=
      DFunLike.congr_fun
        N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap i
    simpa only [map_mul, ha, hi] using hm

end
end MazurProof.N13CoherentChartComparison


