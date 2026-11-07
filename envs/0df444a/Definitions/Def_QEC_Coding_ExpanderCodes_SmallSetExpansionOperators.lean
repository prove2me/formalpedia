-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
-- name    : QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:19:58.633435+00:00
-- url     : https://prove2.me/theorems/2cf3f564-0ea4-495c-b609-542d494c6fe2
-- title:
--   Small Set Expansion Operators
-- statement:
--   Definitions and structural lemmas for Small Set Expansion Operators, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_weightedNeighborSum_eq_degree_mul_sum
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe


set_option autoImplicit false
namespace QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]
def compose (M N : WeightedGraph V) : WeightedGraph V :=
  fun v u => ∑ w, M v w * N w u
theorem weightedNeighborSum_compose (M N : WeightedGraph V) (g : V → ℝ) (v : V) :
    weightedNeighborSum (compose M N) g v =
      weightedNeighborSum M (weightedNeighborSum N g) v := by
  classical
  simp only [weightedNeighborSum, compose, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  ring
theorem HasMeanZeroOperatorBound.compose
    {M N : WeightedGraph V} {lambda mu : ℝ} (degreeN : Nat)
    (hSymmetricN : IsSymmetric N) (hRegularN : IsRegular N degreeN)
    (hM : HasMeanZeroOperatorBound M lambda) (hN : HasMeanZeroOperatorBound N mu) :
    HasMeanZeroOperatorBound (compose M N) (lambda * mu) := by
  intro g hg
  have hMean : (∑ v, weightedNeighborSum N g v) = 0 := by
    rw [sum_weightedNeighborSum_eq_degree_mul_sum N degreeN hSymmetricN hRegularN g,
      hg, mul_zero]
  have hFirst := hM (weightedNeighborSum N g) hMean
  have hSecond := mul_le_mul_of_nonneg_left (hN g hg) (sq_nonneg lambda)
  simp_rw [weightedNeighborSum_compose]
  calc
    _ ≤ lambda ^ 2 * ∑ v, (weightedNeighborSum N g v) ^ 2 := hFirst
    _ ≤ lambda ^ 2 * (mu ^ 2 * ∑ v, (g v) ^ 2) := hSecond
    _ = _ := by ring
end QEC.Coding.SmallSetExpansion


