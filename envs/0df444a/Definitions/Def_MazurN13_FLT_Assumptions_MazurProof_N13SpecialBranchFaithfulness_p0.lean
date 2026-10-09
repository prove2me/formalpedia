-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialBranchFaithfulness_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialBranchFaithfulness_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:05:42.272997+00:00
-- url     : https://prove2.me/theorems/1afc4f1c-00ce-4778-9edf-3bb6e2f3b5bc
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialBranchFaithfulness source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialBranchFaithfulness

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialBranchFaithfulness
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialOverlapBranches_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Each named special branch is faithful on the ordinary coordinate ring.
The norm proves affine faithfulness; localization and the actual overlap
diagram transfer it to the infinity chart. No faithfulness of completion
is postulated.
-/

namespace MazurProof.N13SpecialBranchFaithfulness

noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors

abbrev AO := N13SpecialCurveOverlap.AffineOverlap

theorem affineBranch_injective (negative : Bool) : Function.Injective (affineBranch negative) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra h
  have hn : affineBranch negative (a - b) ≠ 0 := by
    cases negative
    · exact plus_ne_zero _ h
    · exact minus_ne_zero _ h
  apply hn
  simp only [map_sub, hab, sub_self]

private theorem affine_x_ne_zero : N13SpecialCurveOverlap.xClass ≠ 0 :=
  N13GoodCoordinateRingTwo.xClass_ne_zero Polynomial.X_ne_zero

private instance instIsDomainAO : IsDomain AO := IsLocalization.isDomain_localization
  (powers_le_nonZeroDivisors_of_noZeroDivisors affine_x_ne_zero)

private theorem localization_hom_injective
    {A S T : Type*} [CommRing A] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (f : S →+* T) (hf : Function.Injective (f.comp (algebraMap A S))) :
    Function.Injective f := by
  have hzero (z : S) (hz : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M z
    have hfa : f (algebraMap A S a) = 0 := by rw [← ha, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hf (by simpa using hfa)
    rw [ha0, map_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right (IsLocalization.map_units S s).ne_zero
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by simp [map_sub, hab]))

theorem overlapBranch_injective (negative : Bool) : Function.Injective (overlapBranch negative) := by
  have hi : Function.Injective
      ((overlapBranch negative).comp N13SpecialCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13SpecialCurveOverlap.xClass)
    intro a b hab
    apply affineBranch_injective negative
    change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO a)) =
      overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO b)) at hab
    simpa only [N13SpecialCurveOverlap.overlapEquiv_apply,
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      overlapBranch_affine] using hab
  intro a b hab
  apply N13SpecialCurveOverlap.overlapEquiv.symm.injective
  apply hi
  change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm a)) =
    overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm b))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hab

theorem infinity_t_ne_zero : N13SpecialInfinityChart.tClass ≠ 0 := by
  have hd : N13SpecialInfinityChart.curvePoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree N13SpecialInfinityChart.curvePoly_monic.ne_zero,
      N13SpecialInfinityChart.curvePoly_natDegree]
    norm_num
  change AdjoinRoot.of N13SpecialInfinityChart.curvePoly X ≠ 0
  simpa only [map_zero] using
    (AdjoinRoot.of.injective_of_degree_ne_zero hd).ne (Polynomial.X_ne_zero : (X : K[X]) ≠ 0)

theorem infinityBranch_injective (negative : Bool) : Function.Injective (infinityBranch negative) := by
  intro a b hab
  apply IsLocalization.injective O
    (powers_le_nonZeroDivisors_of_noZeroDivisors infinity_t_ne_zero)
  apply overlapBranch_injective negative
  simpa only [overlapBranch_infinity] using congrArg includeSeries hab

theorem infinityBranch_ne_zero (negative : Bool) (b : B) (hb : b ≠ 0) : infinityBranch negative b ≠ 0 := by
  simpa only [map_zero] using (infinityBranch_injective negative).ne hb

end
end MazurProof.N13SpecialBranchFaithfulness


