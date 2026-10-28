-- Prove2me | Definitions.Def_BS2_b3ba934b_NegativeGreedy
-- name    : BS2_b3ba934b_NegativeGreedy
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:25:04.43042+00:00
-- url     : https://prove2.me/theorems/8df5e728-f5fe-4532-bdd9-f994d4eeab59
-- title:
--   Sensitivity separation: NegativeGreedy (complete source module)
-- statement:
--   Complete Lean source module `NegativeGreedy` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/NegativeGreedy.lean; original SHA-256 5d591347757157ea91e7a6c13a8849f18c8e5d37b0527529c1745649fc53c0e9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The exact negative allocation in the numeric recurrence dominates every
actual count vector satisfying its simultaneous prefix constraints. -/
import Definitions.Def_BS2_b3ba934b_PrefixGreedy
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundNegativeGreedy
open ThreeBoundNumeric ThreeBoundGreedy
open scoped BigOperators

theorem negative_weighted (caps : Caps) (r : Q2Record) (q : ℕ) (hq : q ≤ 2)
    (count cost : ℕ → ℕ)
    (hp : ∀ k, k ≤ q → (∑ b ∈ Finset.range (k+1), count b) ≤
      capPrefix caps r k-positivePrefix r k)
    (ha : ∀ k, k+1 ≤ q → cost (k+1) ≤ cost k) :
    (∑ b ∈ Finset.range (q+1), count b*cost b) ≤
      ((List.range (q+1)).map fun b => negativeCount caps q r b*cost b).sum := by
  have h0 := hp 0 (by omega)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h0
  interval_cases q
  · simpa [negativeCount,suffixCapacity,interval] using Nat.mul_le_mul_right (cost 0) h0
  · have h1 := hp 1 (by omega)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h1
    have hh := greedy_two (count 0) (count 1)
      (capPrefix caps r 0-positivePrefix r 0) (capPrefix caps r 1-positivePrefix r 1)
      (cost 0) (cost 1) h0 h1 (ha 0 (by omega))
    simpa [negativeCount,suffixCapacity,interval,List.range_succ,Finset.sum_range_succ,
      min_assoc,min_comm,min_left_comm,Nat.add_assoc] using hh
  · have h1 := hp 1 (by omega)
    have h2 := hp 2 (by omega)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h1 h2
    let c0 := capPrefix caps r 0-positivePrefix r 0
    let c1 := capPrefix caps r 1-positivePrefix r 1
    let c2 := capPrefix caps r 2-positivePrefix r 2
    have he : min c0 (min c1 c2)+(min c1 c2-min c0 (min c1 c2)) = min c1 c2 := by omega
    have hh := greedy_three (count 0) (count 1) (count 2) c0 c1 c2
      (cost 0) (cost 1) (cost 2) h0 h1 h2 (ha 0 (by omega)) (ha 1 (by omega))
    dsimp only at hh
    rw [he] at hh
    simpa [negativeCount,suffixCapacity,interval,List.range_succ,Finset.sum_range_succ,
      min_assoc,min_comm,min_left_comm,Nat.add_assoc,c0,c1,c2] using hh

end ThreeBoundNegativeGreedy

#print axioms ThreeBoundNegativeGreedy.negative_weighted


