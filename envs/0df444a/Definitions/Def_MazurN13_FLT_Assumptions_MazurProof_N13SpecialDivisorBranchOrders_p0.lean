-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorBranchOrders_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorBranchOrders_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:07:23.32793+00:00
-- url     : https://prove2.me/theorems/13ee6649-5a4e-4b97-aa20-1128d9f6c4a7
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialDivisorBranchOrders
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialBranchFaithfulness_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Compute the actual special infinity ideals of rational-point divisors under
both named branch maps. The finite-degree and two infinity counts add to
the total degree. A principal ideal equation therefore gives an exact
Laurent-order balance, not a guessed sheet assignment.
-/

namespace MazurProof.N13SpecialDivisorBranchOrders

noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2

@[simp] theorem infinityBranch_t (negative : Bool) :
    infinityBranch negative N13SpecialInfinityChart.tClass = PowerSeries.X := by
  cases negative <;> simp [infinityBranch]

@[simp] theorem infinityBranch_constant (negative : Bool) (a : K) :
    infinityBranch negative (algebraMap K[X] B (C a)) = PowerSeries.C a := by
  cases negative
  · change N13SpecialInfinityBranchJets.plus
      (N13IntegralInfinityReduction.specialBaseClass (C a)) = _
    rw [N13SpecialInfinityBranchJets.plus_base]
    simp [N13SpecialInfinityBranchJets.beta]
  · change N13SpecialInfinityBranchJets.minus
      (N13IntegralInfinityReduction.specialBaseClass (C a)) = _
    rw [N13SpecialInfinityBranchJets.minus_base]
    simp [N13SpecialInfinityBranchJets.beta]

private theorem branch_finite_point (negative : Bool) (v : K) :
    Ideal.map (infinityBranch negative) (infinityPointIdeal 1 v) = ⊤ := by
  let I := Ideal.map (infinityBranch negative) (infinityPointIdeal 1 v)
  have hm : PowerSeries.X - PowerSeries.C (1 : K) ∈ I := by
    have hmem : N13SpecialInfinityChart.tClass - algebraMap K[X] B (C (1 : K)) ∈
        infinityPointIdeal 1 v := Ideal.subset_span (by simp)
    simpa only [map_sub, infinityBranch_t, infinityBranch_constant] using
      Ideal.mem_map_of_mem (infinityBranch negative) hmem
  have hu : IsUnit (PowerSeries.X - PowerSeries.C (1 : K) : P) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using (isUnit_neg_one : IsUnit (-1 : K))
  exact I.eq_top_of_isUnit_mem hm hu

def pointOrder (negative : Bool) : CurvePoint → ℕ
  | Sum.inl _ => 0
  | Sum.inr P => if P.1 = (if negative then 1 else 0) then 1 else 0

theorem point_branch_ideal (negative : Bool) (P : CurvePoint) :
    Ideal.map (infinityBranch negative) (point P).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ pointOrder negative P} : Set N13SpecialLaurentBranches.P) := by
  cases P with
  | inl P =>
    change Ideal.map (infinityBranch negative) (point (Sum.inl P)).infinityIdeal = _
    simp only [pointOrder, pow_zero, Ideal.span_singleton_one]
    unfold point
    split
    · simp [affineZeroPoint, Ideal.map_top]
    · exact branch_finite_point negative P.1.2
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv
    · cases negative
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.plus_positive_point
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.minus_positive_point
    · cases negative
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.plus_negative_point
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.minus_negative_point

theorem point_degree_balance (P : CurvePoint) :
    (pointPolynomial P).natDegree + pointOrder false P + pointOrder true P = 1 := by
  cases P with
  | inl P => simp [pointPolynomial, pointOrder]
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv <;>
      simp [pointPolynomial, pointOrder, hv]

def divisorOrder (negative : Bool) : EffectiveDivisorTwo → ℕ :=
  Sym2.lift ⟨fun P Q => pointOrder negative P + pointOrder negative Q, fun P Q => Nat.add_comm _ _⟩

@[simp] theorem divisorOrder_mk (negative : Bool) (P Q : CurvePoint) :
    divisorOrder negative s(P, Q) = pointOrder negative P + pointOrder negative Q := rfl

theorem divisor_branch_ideal (negative : Bool) (D : EffectiveDivisorTwo) :
    Ideal.map (infinityBranch negative) (ofDivisor D).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ divisorOrder negative D} : Set N13SpecialLaurentBranches.P) := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change Ideal.map (infinityBranch negative) ((point P).infinityIdeal * (point Q).infinityIdeal) = _
  rw [Ideal.map_mul, point_branch_ideal, point_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl

theorem divisor_degree_balance (D : EffectiveDivisorTwo) :
    (divisorPolynomial D).natDegree + divisorOrder false D + divisorOrder true D = 2 := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [divisorPolynomial_mk, Polynomial.natDegree_mul
    (pointPolynomial_monic P).ne_zero (pointPolynomial_monic Q).ne_zero,
    divisorOrder_mk, divisorOrder_mk]
  have hp := point_degree_balance P
  have hq := point_degree_balance Q
  omega

def tensorOrder (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  divisorOrder negative D + divisorOrder negative E

theorem tensor_branch_ideal (negative : Bool) (D E : EffectiveDivisorTwo) :
    Ideal.map (infinityBranch negative) (tensor (ofDivisor D) (ofDivisor E)).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ tensorOrder negative D E} : Set N13SpecialLaurentBranches.P) := by
  change Ideal.map (infinityBranch negative) ((ofDivisor D).infinityIdeal * (ofDivisor E).infinityIdeal) = _
  rw [Ideal.map_mul, divisor_branch_ideal, divisor_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl

theorem tensor_degree_balance (D E : EffectiveDivisorTwo) :
    (tensorPolynomial D E).natDegree + tensorOrder false D E + tensorOrder true D E = 4 := by
  rw [tensorPolynomial, Polynomial.natDegree_mul
    (divisorPolynomial_monic D).ne_zero (divisorPolynomial_monic E).ne_zero]
  have hd := divisor_degree_balance D
  have he := divisor_degree_balance E
  unfold tensorOrder
  omega

end
end MazurProof.N13SpecialDivisorBranchOrders


