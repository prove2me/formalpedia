-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialOverlapBranches_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialOverlapBranches_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:59:33.193301+00:00
-- url     : https://prove2.me/theorems/450f3a87-9d9b-4819-be47-88aa1ef12560
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialOverlapBranches source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialOverlapBranches

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialOverlapBranches
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialLaurentBranches_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The actual special ordinary overlap maps to each Laurent branch. The maps
agree with the just-constructed affine expansions and with the inclusions
of the actual infinity power-series expansions. Consequently a special
comparison transports one and the same fraction to both branches.
-/

namespace MazurProof.N13SpecialOverlapBranches

noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries

abbrev B := N13SpecialInfinityChart.CoordinateRing
abbrev O := N13SpecialCurveOverlap.InfinityOverlap

def infinityBranch (negative : Bool) : B →+* P :=
  if negative then N13SpecialInfinityBranchJets.minus else N13SpecialInfinityBranchJets.plus

def affineBranch (negative : Bool) : R →+* L := if negative then minus else plus

theorem branch_base (negative : Bool) (p : K[X]) :
    includeSeries (infinityBranch negative (algebraMap K[X] B p)) =
      p.eval₂ (algebraMap K L) t := by
  cases negative
  · change includeSeries (N13SpecialInfinityBranchJets.plus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.plus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
  · change includeSeries (N13SpecialInfinityBranchJets.minus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.minus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm

private theorem t_isUnit (negative : Bool) :
    IsUnit ((includeSeries.comp (infinityBranch negative)) N13SpecialInfinityChart.tClass) := by
  change IsUnit (includeSeries (infinityBranch negative (algebraMap K[X] B X)))
  rw [branch_base]
  simpa using (isUnit_iff_ne_zero.mpr t_ne_zero : IsUnit t)

def overlapBranch (negative : Bool) : O →+* L :=
  IsLocalization.Away.lift N13SpecialInfinityChart.tClass (t_isUnit negative)

@[simp] theorem overlapBranch_infinity (negative : Bool) (b : B) :
    overlapBranch negative (algebraMap B O b) = includeSeries (infinityBranch negative b) :=
  DFunLike.congr_fun
    (IsLocalization.Away.lift_comp N13SpecialInfinityChart.tClass (t_isUnit negative)) b

@[simp] theorem overlapBranch_t (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.tOverlap = t := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B X)) = _
  rw [overlapBranch_infinity, branch_base]
  simp

@[simp] theorem overlapBranch_x (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.xOverlap = t⁻¹ := by
  have he := congrArg (overlapBranch negative) N13SpecialCurveOverlap.tOverlap_mul_xOverlap
  rw [map_mul, overlapBranch_t, map_one] at he
  apply mul_left_cancel₀ t_ne_zero
  rw [he, mul_inv_cancel₀ t_ne_zero]

@[simp] theorem overlapBranch_coefficient (negative : Bool) (a : K) :
    overlapBranch negative (N13SpecialCurveOverlap.coefficientToInfinityOverlap a) =
      algebraMap K L a := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B (C a))) = _
  rw [overlapBranch_infinity, branch_base]
  simp

private theorem base_X' : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

theorem overlapBranch_affine_hom (negative : Bool) :
    (overlapBranch negative).comp N13SpecialCurveOverlap.affineToInfinityOverlap =
      affineBranch negative := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap
          (AdjoinRoot.of N13GoodCoordinateRingTwo.curvePoly (C a))) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass (C a))
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_of]
      simp only [N13SpecialCurveOverlap.affineCoeffMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [overlapBranch_coefficient]
      cases negative <;> simp [affineBranch, base, N13BranchNorm.evalPoly]
    · change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.xClass) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass X)
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_xClass, overlapBranch_x]
      cases negative
      · simp only [affineBranch, Bool.false_eq_true, if_false, plus_xClass, base_X']
      · simp only [affineBranch, if_true, minus_xClass, base_X']
  · change overlapBranch negative
      (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.yClass) =
      affineBranch negative N13GoodCoordinateRingTwo.yClass
    rw [N13SpecialCurveOverlap.affineToInfinityOverlap_yClass]
    change overlapBranch negative (N13SpecialCurveOverlap.xOverlap ^ 3 *
      algebraMap B O N13SpecialInfinityChart.vClass) = _
    rw [map_mul, map_pow, overlapBranch_x, overlapBranch_infinity]
    cases negative
    · simp only [affineBranch, infinityBranch, Bool.false_eq_true, if_false, plus_yClass,
        N13SpecialInfinityBranchJets.plus_v]
    · simp only [affineBranch, infinityBranch, if_true, minus_yClass,
        N13SpecialInfinityBranchJets.minus_v]

@[simp] theorem overlapBranch_affine (negative : Bool) (a : R) :
    overlapBranch negative (N13SpecialCurveOverlap.affineToInfinityOverlap a) =
      affineBranch negative a := DFunLike.congr_fun (overlapBranch_affine_hom negative) a

theorem cross_relation (negative : Bool) (a b : R) (c d : B)
    (h : N13SpecialCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13SpecialCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    affineBranch negative a * includeSeries (infinityBranch negative d) =
      affineBranch negative b * includeSeries (infinityBranch negative c) := by
  simpa only [map_mul, overlapBranch_affine, overlapBranch_infinity] using
    congrArg (overlapBranch negative) h

end
end MazurProof.N13SpecialOverlapBranches


