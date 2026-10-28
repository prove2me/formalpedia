-- Prove2me | Definitions.Def_BS2_b3ba934b_GradedCandidates
-- name    : BS2_b3ba934b_GradedCandidates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:05:38.570995+00:00
-- url     : https://prove2.me/theorems/d7d4d098-193a-478f-9888-aef72119705b
-- title:
--   Sensitivity separation: GradedCandidates (complete source module)
-- statement:
--   Complete Lean source module `GradedCandidates` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GradedCandidates.lean; original SHA-256 b678c8d2d17ede20517cee0be5f70571b803e9e5a8ee20483d5fef6346a7243d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual weak rejection constraints for the q2 head-cost formulas. -/
import Definitions.Def_BS2_b3ba934b_HeadCosts
import Definitions.Def_BS2_b3ba934b_GradedRepairCover

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

structure PairData (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) where
  weak : ℕ → L
  strong : ℕ → L
  weakMono : Monotone weak
  strongMono : Monotone strong
  guards : S.guard j ≤ S.guard i
  tolerances : S.tolerance j ≤ S.tolerance i
  targets : ∀ b, b ≤ S.tolerance j → weak b ≤ strong b
  weakDef : ∀ d u z, S.target i d u z = (F (weak d) u && F (weak d) z)
  strongDef : ∀ d u z, S.target j d u z = (F (strong d) u && F (strong d) z)
  guardTarget : ∀ b, b ≤ S.tolerance j → S.guard j ≤ strong b
  weakGuardTarget : ∀ b, b ≤ S.tolerance i → S.guard i ≤ weak b

variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem failed_weak_subset (v : V) : failed S F i x v ⊆ failed S F j x v := by
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨_,hR,htrue⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hF _ _ P.guards _ htrue⟩

theorem weak_accepts_of_strong_targets (v : V) (b : ℕ)
    (hb : b ≤ S.tolerance j) (hc : (failed S F i x v).card ≤ b)
    (ht : ∀ c, F (P.strong b) (child x v c) = true) : parent S F i x = true := by
  apply parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono P.weakDef
    x v b (hb.trans P.tolerances) hc
  · exact hF _ _ (P.targets b hb) _ (ht false)
  · exact hF _ _ (P.targets b hb) _ (ht true)

theorem strong_false_of_weak_false (hoff : parent S F i x = false) :
    parent S F j x = false := by
  cases hon : parent S F j x with
  | false => rfl
  | true =>
      obtain ⟨v,hb,ht⟩ := (parent_true_iff S F j x).1 hon
      have hboth : ∀ c, F (P.strong (failed S F j x v).card) (child x v c) = true := by
        rw [P.strongDef] at ht
        intro c
        cases c <;> simp_all
      have he := weak_accepts_of_strong_targets S F hF i j P x v _ hb
        (Finset.card_le_card (failed_weak_subset S F hF i j P x v)) hboth
      rw [hoff] at he
      contradiction

/-- At an actual target candidate, its missing child fails the weak same-tier
    target. Otherwise the weak row would already accept at its lower count. -/
theorem target_missing_weak_false (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (c : Bool) (hb : b ≤ S.tolerance j)
    (hc : (failed S F j x v).card = b)
    (hpartner : F (P.strong b) (child x v (!c)) = true) :
    F (P.weak b) (child x v c) = false := by
  cases hmissing : F (P.weak b) (child x v c) with
  | false => rfl
  | true =>
      have hcnt : (failed S F i x v).card ≤ b := by
        rw [← hc]
        exact Finset.card_le_card (failed_weak_subset S F hF i j P x v)
      have hp := hF _ _ (P.targets b hb) _ hpartner
      have hboth : ∀ e, F (P.weak b) (child x v e) = true := by
        cases c <;> intro e <;> cases e <;> assumption
      have he := parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono
        P.weakDef x v b (hb.trans P.tolerances) hcnt (hboth false) (hboth true)
      rw [hoff] at he
      contradiction

/-- An actual guard candidate has exactly the same failed guards for both
    recipes, because one fewer weak failure would already accept. -/
theorem guard_failures_eq (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (hb : b ≤ S.tolerance j)
    (hc : (failed S F j x v).card = b+1)
    (ht : ∀ c, F (P.strong b) (child x v c) = true) :
    failed S F i x v = failed S F j x v := by
  have hsub := failed_weak_subset S F hF i j P x v
  have hle := Finset.card_le_card hsub
  have hn : ¬ (failed S F i x v).card ≤ b := by
    intro hsmall
    have he := weak_accepts_of_strong_targets S F hF i j P x v b hb hsmall ht
    rw [hoff] at he
    contradiction
  apply Finset.eq_of_subset_of_card_le hsub
  omega

theorem guard_hit_eligible (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (hb : b ≤ S.tolerance j)
    (hc : (failed S F j x v).card = b+1)
    (ht : ∀ c, F (P.strong b) (child x v c) = true)
    (w : V) (hw : w ∈ failed S F j x v) :
    F (S.guard i) (child x w (S.label v w)) = true := by
  have he := guard_failures_eq S F hF i j P x hoff v b hb hc ht
  rw [← he] at hw
  exact (Finset.mem_filter.mp hw).2.2

/-- The next weak component forbids a guard candidate whenever its targets
    are implied by the strong previous targets. -/
theorem no_guard_candidate_of_next (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (hc : (failed S F j x v).card = b+1)
    (ht : ∀ c, F (P.strong b) (child x v c) = true)
    (hb : b+1 ≤ S.tolerance i) (hnext : P.weak (b+1) ≤ P.strong b) : False := by
  have hcount : (failed S F i x v).card ≤ b+1 := by
    rw [← hc]
    exact Finset.card_le_card (failed_weak_subset S F hF i j P x v)
  have he := parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono
    P.weakDef x v (b+1) hb hcount
      (hF _ _ hnext _ (ht false)) (hF _ _ hnext _ (ht true))
  rw [hoff] at he
  contradiction

theorem guard_next_weak_false (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (hc : (failed S F j x v).card = b+1)
    (hb : b+1 ≤ S.tolerance i) :
    F (P.weak (b+1)) (child x v false) = false ∨
      F (P.weak (b+1)) (child x v true) = false := by
  by_cases h0 : F (P.weak (b+1)) (child x v false) = true
  · by_cases h1 : F (P.weak (b+1)) (child x v true) = true
    · have hcount : (failed S F i x v).card ≤ b+1 := by
        rw [← hc]
        exact Finset.card_le_card (failed_weak_subset S F hF i j P x v)
      have he := parent_true_of_count_bound S F hF (fun _ => P.weak) i P.weakMono
        P.weakDef x v (b+1) hb hcount h0 h1
      rw [hoff] at he
      contradiction
    · exact Or.inr (Bool.eq_false_iff.mpr h1)
  · exact Or.inl (Bool.eq_false_iff.mpr h0)

end
end ThreeBoundGradedCandidates

#print axioms ThreeBoundGradedCandidates.target_missing_weak_false
#print axioms ThreeBoundGradedCandidates.guard_failures_eq
#print axioms ThreeBoundGradedCandidates.no_guard_candidate_of_next
#print axioms ThreeBoundGradedCandidates.guard_next_weak_false


