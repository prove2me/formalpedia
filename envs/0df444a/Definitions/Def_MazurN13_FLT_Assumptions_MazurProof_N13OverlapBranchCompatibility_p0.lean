-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OverlapBranchCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OverlapBranchCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:40:10.756617+00:00
-- url     : https://prove2.me/theorems/7fcb0307-6b7f-48ac-8271-4ea003abd967
-- title:
--   FLT.Assumptions.MazurProof.N13OverlapBranchCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OverlapBranchCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OverlapBranchCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveChartTransport_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityChartMarking_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryCompletionCompatibility_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAffineRestrictionCompatibility_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The actual ordinary overlap has two faithful rational Laurent branch maps.
Their affine restrictions are the named function-field expansions; their
infinity restrictions are the inclusions of the named power-series maps.
Thus the primitive chart transport gives the SAME fraction on BOTH branches.
-/

namespace MazurProof.N13OverlapBranchCompatibility

noncomputable section
open scoped nonZeroDivisors LaurentSeries
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Q₂ := N13TwoAdicInfinityCompatibility.Q₂
abbrev A := N13OrdinaryCurveOverlap.AffineCurve
abbrev B := N13OrdinaryCurveOverlap.InfinityCurve
abbrev AO := N13OrdinaryCurveOverlap.AffineOverlap
abbrev O := N13OrdinaryCurveOverlap.InfinityOverlap
abbrev L := N13TwoAdicInfinityCompatibility.RationalLaurent
abbrev QP := N13TwoAdicInfinityCompatibility.RationalPower

def includePower : QP →+* L := HahnSeries.ofPowerSeries ℤ Q₂

def overlapBranches : O →+* L × L :=
  N13TwoAdicAffineRestrictionCompatibility.laurentPairMap.comp
    (N13FormalOverlapSplit.formalBranchEval.comp
      N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve)

def positiveOverlap : O →+* L := (RingHom.fst L L).comp overlapBranches
def negativeOverlap : O →+* L := (RingHom.snd L L).comp overlapBranches

theorem overlapBranches_affine (a : A) :
    overlapBranches (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13TwoInfinityRestriction.coordinateToBranches Q₂
        (N13IntegralFractionalHull.integralToRational a) := by
  have h := DFunLike.congr_fun
    N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve_comp_affine a
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a))) = _
  have h' : N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
      (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13FormalCurveOverlap.affineToFormalCurve a := h
  rw [h']
  exact N13TwoAdicAffineRestrictionCompatibility.affineRestriction_commutes a

theorem overlapBranches_infinity (b : B) :
    overlapBranches (algebraMap B O b) =
      (includePower (N13InfinityChartMarking.positiveExpansion b),
        includePower (N13InfinityChartMarking.negativeExpansion b)) := by
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
        (algebraMap B O b))) = _
  rw [N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve_algebraMap]
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13FormalInfinityChart.infinityToFormalCurve
        (N13IntegralInfinityChart.toFormalInfinity b))) = _
  rw [N13FormalOverlapSplit.formalBranchEval_infinityToFormalCurve]
  apply Prod.ext
  · exact N13TwoAdicInfinityCompatibility.laurentMap_includePower
      (N13InfinityChartMarking.positiveIntegralExpansion b)
  · exact N13TwoAdicInfinityCompatibility.laurentMap_includePower
      (N13InfinityChartMarking.negativeIntegralExpansion b)

@[simp] theorem positiveOverlap_affine (a : A) :
    positiveOverlap (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13Infinity.coordinateToLaurent Q₂
        (N13IntegralFractionalHull.integralToRational a) :=
  congrArg Prod.fst (overlapBranches_affine a)

@[simp] theorem negativeOverlap_affine (a : A) :
    negativeOverlap (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13InfinityMinus.coordinateToLaurentMinus Q₂
        (N13IntegralFractionalHull.integralToRational a) :=
  congrArg Prod.snd (overlapBranches_affine a)

@[simp] theorem positiveOverlap_infinity (b : B) :
    positiveOverlap (algebraMap B O b) =
      includePower (N13InfinityChartMarking.positiveExpansion b) :=
  congrArg Prod.fst (overlapBranches_infinity b)

@[simp] theorem negativeOverlap_infinity (b : B) :
    negativeOverlap (algebraMap B O b) =
      includePower (N13InfinityChartMarking.negativeExpansion b) :=
  congrArg Prod.snd (overlapBranches_infinity b)

private theorem localization_hom_injective
    {R S T : Type*} [CommRing R] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (f : S →+* T) (hf : Function.Injective (f.comp (algebraMap R S))) :
    Function.Injective f := by
  have hzero (z : S) (hz : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M z
    have hfa : f (algebraMap R S a) = 0 := by
      rw [← ha, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hf (by simpa using hfa)
    rw [ha0, map_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right (IsLocalization.map_units S s).ne_zero
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by simp [map_sub, hxy]))

theorem positiveOverlap_injective : Function.Injective positiveOverlap := by
  have h : Function.Injective
      (positiveOverlap.comp N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
    have hi := (N13Infinity.coordinateToLaurent_injective Q₂).comp
      N13IntegralFractionalHull.integralToRational_injective
    intro a b hab
    apply hi
    change positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO a)) =
      positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO b)) at hab
    simp only [N13OrdinaryCurveOverlap.overlapEquiv_apply,
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      positiveOverlap_affine] at hab
    exact hab
  intro x y hxy
  apply N13OrdinaryCurveOverlap.overlapEquiv.symm.injective
  apply h
  change positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm x)) =
    positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm y))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hxy

theorem negativeOverlap_injective : Function.Injective negativeOverlap := by
  have h : Function.Injective
      (negativeOverlap.comp N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
    have hi := (N13InfinityMinus.coordinateToLaurentMinus_injective Q₂).comp
      N13IntegralFractionalHull.integralToRational_injective
    intro a b hab
    apply hi
    change negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO a)) =
      negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO b)) at hab
    simp only [N13OrdinaryCurveOverlap.overlapEquiv_apply,
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      negativeOverlap_affine] at hab
    exact hab
  intro x y hxy
  apply N13OrdinaryCurveOverlap.overlapEquiv.symm.injective
  apply h
  change negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm x)) =
    negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm y))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hxy

theorem positiveExpansion_injective :
    Function.Injective N13InfinityChartMarking.positiveExpansion := by
  intro a b hab
  apply N13IntegralCurveProperties.infinity_to_overlap_injective
  apply positiveOverlap_injective
  simpa only [positiveOverlap_infinity] using congrArg includePower hab

theorem negativeExpansion_injective :
    Function.Injective N13InfinityChartMarking.negativeExpansion := by
  intro a b hab
  apply N13IntegralCurveProperties.infinity_to_overlap_injective
  apply negativeOverlap_injective
  simpa only [negativeOverlap_infinity] using congrArg includePower hab

/-- Exact chart transport commutes with both branches, with no independent
choice of numerator, denominator, or rational function on either branch. -/
theorem branch_cross_relations (a b : A) (c d : B)
    (h : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    N13Infinity.coordinateToLaurent Q₂ (N13IntegralFractionalHull.integralToRational a) *
        includePower (N13InfinityChartMarking.positiveExpansion d) =
      N13Infinity.coordinateToLaurent Q₂ (N13IntegralFractionalHull.integralToRational b) *
        includePower (N13InfinityChartMarking.positiveExpansion c) ∧
    N13InfinityMinus.coordinateToLaurentMinus Q₂ (N13IntegralFractionalHull.integralToRational a) *
        includePower (N13InfinityChartMarking.negativeExpansion d) =
      N13InfinityMinus.coordinateToLaurentMinus Q₂ (N13IntegralFractionalHull.integralToRational b) *
        includePower (N13InfinityChartMarking.negativeExpansion c) := by
  constructor
  · simpa only [map_mul, positiveOverlap_affine, positiveOverlap_infinity]
      using congrArg positiveOverlap h
  · simpa only [map_mul, negativeOverlap_affine, negativeOverlap_infinity]
      using congrArg negativeOverlap h

end
end MazurProof.N13OverlapBranchCompatibility


