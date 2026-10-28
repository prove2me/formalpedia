-- Prove2me | Definitions.Def_BS2_b3ba934b_RecordCapStats
-- name    : BS2_b3ba934b_RecordCapStats
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:35:58.898053+00:00
-- url     : https://prove2.me/theorems/5570a56e-77fc-4d8d-a34d-2f6ca5894ea1
-- title:
--   Sensitivity separation: RecordCapStats (complete source module)
-- statement:
--   Complete Lean source module `RecordCapStats` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecordCapStats.lean; original SHA-256 ed833e3308d481a66dfa0991dfe1e540a9627d5a4f82a610e495716c925c454e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The numerical type-count combinations are exact cardinalities of actual
candidate prefixes and eligible marker sets. -/
import Definitions.Def_BS2_b3ba934b_TagPrefixFacts
import Definitions.Def_BS2_b3ba934b_CapAlgorithm
import Definitions.Def_BS2_b3ba934b_TypeCountSums
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundRecordCaps
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]

theorem kindBudget_eq (k : Fin 8) : kindBudget k.val = ThreeBoundQ2.budget k := by
  fin_cases k <;> rfl

theorem positiveInside_eq (k : Fin 8) (q : ℕ) :
    positiveInside k.val q = ThreeBoundQ2.positivePrefix q k := by
  fin_cases k <;> simp [positiveInside,ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel]

theorem lowCount_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) :
    lowCount x q = (H.filter fun w =>
      ThreeBoundQ2.positivePrefix q (tag w) = false ∧ ThreeBoundQ2.budget (tag w) ≤ q).card := by
  have he := card_filter_tag H tag (fun k =>
    ThreeBoundQ2.positivePrefix q k = false ∧ ThreeBoundQ2.budget k ≤ q)
  trans ∑ k : Fin 8, if ThreeBoundQ2.positivePrefix q k = false ∧
      ThreeBoundQ2.budget k ≤ q then typeCount H tag k else 0
  · unfold lowCount
    rw [sum_filterMap_eight]
    apply Finset.sum_congr rfl
    intro k _
    simp only [positiveInside_eq,kindBudget_eq,hx]
    cases ThreeBoundQ2.positivePrefix q k <;> simp
  · convert he.symm using 1 <;> congr 1 <;> ext a <;> simp

theorem nextCount_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) :
    nextCount x q = (H.filter fun w =>
      ThreeBoundQ2.positivePrefix q (tag w) = false ∧ ThreeBoundQ2.budget (tag w) ≤ q+1).card := by
  have he := card_filter_tag H tag (fun k =>
    ThreeBoundQ2.positivePrefix q k = false ∧ ThreeBoundQ2.budget k ≤ q+1)
  trans ∑ k : Fin 8, if ThreeBoundQ2.positivePrefix q k = false ∧
      ThreeBoundQ2.budget k ≤ q+1 then typeCount H tag k else 0
  · unfold nextCount
    rw [sum_filterMap_eight]
    apply Finset.sum_congr rfl
    intro k _
    simp only [positiveInside_eq,kindBudget_eq,hx]
    cases ThreeBoundQ2.positivePrefix q k <;> simp
  · convert he.symm using 1 <;> congr 1 <;> ext a <;> simp

theorem eligibleCount_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) :
    eligibleCount x q = (H.filter fun w => ThreeBoundQ2.budget (tag w) ≤ q+1).card := by
  have he := card_filter_tag H tag (fun k => ThreeBoundQ2.budget k ≤ q+1)
  trans ∑ k : Fin 8, if ThreeBoundQ2.budget k ≤ q+1 then typeCount H tag k else 0
  · unfold eligibleCount
    rw [sum_filterMap_eight]
    apply Finset.sum_congr rfl
    intro k _
    simp only [kindBudget_eq,hx]
  · convert he.symm using 1 <;> congr 1 <;> ext a <;> simp

theorem headCount_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) : headCount x = H.card := by
  have he : headCount x = ∑ k : Fin 8, x k.val := by
    simp [headCount,List.range_succ,Fin.sum_univ_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [he]
  simpa only [hx] using sum_typeCounts H tag

theorem positivePrefix_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) (hq : q ≤ 2) :
    positivePrefix x q = (H.filter fun w => ThreeBoundQ2.positivePrefix q (tag w) = true).card := by
  have hec := card_filter_tag H tag (fun k => ThreeBoundQ2.positivePrefix q k = true)
  trans ∑ k : Fin 8, if ThreeBoundQ2.positivePrefix q k = true then typeCount H tag k else 0
  swap
  · convert hec.symm using 1 <;> congr 1 <;> ext a <;> simp
  have he : ∀ k : Fin 8, typeCount H tag k = x k.val := fun k => (hx k).symm
  simp only [he]
  interval_cases q <;>
    simp [positivePrefix,positiveCount,ThreeBoundQ2.positivePrefix,ThreeBoundQ2.positiveLevel,
      List.range_succ,Fin.sum_univ_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end
end ThreeBoundRecordCaps

#print axioms ThreeBoundRecordCaps.positivePrefix_card


