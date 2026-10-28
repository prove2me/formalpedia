-- Prove2me | Definitions.Def_BS2_b3ba934b_RecordAllowedAlgorithm
-- name    : BS2_b3ba934b_RecordAllowedAlgorithm
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:24:29.491208+00:00
-- url     : https://prove2.me/theorems/0e584db2-0ea5-40b0-a8c0-09a532b43cab
-- title:
--   Sensitivity separation: RecordAllowedAlgorithm (complete source module)
-- statement:
--   Complete Lean source module `RecordAllowedAlgorithm` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecordAllowedAlgorithm.lean; original SHA-256 0890dfe0ea7f207a310834ba1791f0d3210cfcaa03b2df0efac350fe6fd48bed; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Q2RawExpressions

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundRecordAllowedAlgorithm
open ThreeBoundNumeric

theorem allowedRecord_of (caps : Caps) (q : ℕ) (r : Q2Record)
    (htol : q=1 → r 2=0 ∧ r 5=0 ∧ r 7=0)
    (hprefix : ∀ k, k ≤ q → positivePrefix r k ≤ capPrefix caps r k) :
    allowedRecord caps q r = true := by
  unfold allowedRecord
  simp only [Bool.and_eq_true]
  constructor
  · by_cases hq : q=1
    · obtain ⟨h2,h5,h7⟩ := htol hq
      simp [hq,h2,h5,h7]
    · simp [hq]
  · apply List.all_eq_true.mpr
    intro k hk
    exact decide_eq_true (hprefix k (Nat.le_of_lt_succ (List.mem_range.mp hk)))

theorem recordAllowedFor_of (caps : Caps) (a c : Entry) (r : Q2Record)
    (hallowed : allowedRecord caps c.tolerance r = true)
    (hguard : ∀ k, k ≤ c.tolerance →
      k < a.tolerance → a.threshold (k+1) ≤ c.threshold k →
      r (3+k)=0 ∧ (k=0 → r 6=0) ∧ (k=1 → r 7=0))
    (hpositive : ∀ k, k ≤ c.tolerance → r k≠0 →
      c.guard ≠ (if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))) :
    recordAllowedFor caps a c r = true := by
  unfold recordAllowedFor
  simp only [Bool.and_eq_true]
  constructor
  · refine ⟨hallowed,?_⟩
    apply List.all_eq_true.mpr
    intro k hk
    have hk' : k ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hk)
    by_cases he : k < a.tolerance ∧ a.threshold (k+1) ≤ c.threshold k
    · obtain ⟨hg,h0,h1⟩ := hguard k hk' he.1 he.2
      simp only [he,decide_true,Bool.not_true,Bool.false_or,hg,beq_self_eq_true,Bool.true_and]
      split_ifs with hz ho
      · simp [h0 hz]
      · simp [h1 ho]
      · rfl
    · simp [he]
  · apply List.all_eq_true.mpr
    intro k hk
    have hk' : k ≤ c.tolerance := Nat.le_of_lt_succ (List.mem_range.mp hk)
    by_cases hz : r k=0
    · simp [hz]
    · have he := hpositive k hk' hz
      simpa [hz] using he

end ThreeBoundRecordAllowedAlgorithm

#print axioms ThreeBoundRecordAllowedAlgorithm.recordAllowedFor_of


