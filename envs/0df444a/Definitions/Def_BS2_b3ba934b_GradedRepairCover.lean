-- Prove2me | Definitions.Def_BS2_b3ba934b_GradedRepairCover
-- name    : BS2_b3ba934b_GradedRepairCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:03:43.66822+00:00
-- url     : https://prove2.me/theorems/61b8ee4b-00e3-4755-bf54-4f5f6b8397f5
-- title:
--   Sensitivity separation: GradedRepairCover (complete source module)
-- statement:
--   Complete Lean source module `GradedRepairCover` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GradedRepairCover.lean; original SHA-256 bfcd268a458caa3bfb864a57dc0542e3f1d714ae6c40a6026503f9cbf2c93dab; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Actual parent one-bit repairs are covered by the graded target/guard candidates.
This connects the concrete Boolean functions to the finite q2 type analysis.
-/
import Definitions.Def_BS2_b3ba934b_GradedPositiveBoundary
import Definitions.Def_BS2_b3ba934b_Q2CandidateTypes

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundRepair
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {L I V : Type} [Fintype V]

theorem failed_flip_mem_other (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w z : V) (c : Bool) (a : I)
    (h : (z, S.label v z) ≠ (w,c)) :
    z ∈ failed S F l (flip x {((w,c),a)}) v ↔ z ∈ failed S F l x v := by
  simp only [failed, Finset.mem_filter, Finset.mem_univ, true_and,
    child_flip_other x w z c (S.label v z) a h]

theorem failed_flip_own (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (a : I) :
    failed S F l (flip x {((v,c),a)}) v = failed S F l x v := by
  ext z
  by_cases hz : z = v
  · subst z
    simp [failed, S.loopless v]
  · exact failed_flip_mem_other S F l x v v z c a
      (fun h => hz (congrArg Prod.fst h))

theorem failed_before_subset_insert_after (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) :
    failed S F l x v ⊆ insert w (failed S F l (flip x {((w,c),a)}) v) := by
  intro z hz
  by_cases hzw : z = w
  · exact Finset.mem_insert.mpr (Or.inl hzw)
  · exact Finset.mem_insert.mpr (Or.inr
      ((failed_flip_mem_other S F l x v w z c a
        (fun h => hzw (congrArg Prod.fst h))).2 hz))

/-- A strict decrease of the actual guard count removes exactly the changed
    selected guard, and decreases the count by exactly one. -/
theorem failed_decrease (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hdec : (failed S F l (flip x {((w,c),a)}) v).card < (failed S F l x v).card) :
    S.Adj v w ∧ S.label v w = c ∧
      F (S.guard l) (child x w c) = true ∧
      F (S.guard l) (flip (child x w c) {a}) = false ∧
      (failed S F l x v).card = (failed S F l (flip x {((w,c),a)}) v).card+1 := by
  have hsubset := failed_before_subset_insert_after S F l x v w c a
  have hcard : (failed S F l x v).card ≤ (failed S F l (flip x {((w,c),a)}) v).card+1 :=
    (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
  have hwold : w ∈ failed S F l x v := by
    by_contra hn
    have hsub : failed S F l x v ⊆ failed S F l (flip x {((w,c),a)}) v := by
      intro z hz
      rcases Finset.mem_insert.mp (hsubset hz) with hzw | hh
      · exact False.elim (hn (hzw ▸ hz))
      · exact hh
    exact (Nat.not_le_of_lt hdec) (Finset.card_le_card hsub)
  have hwnew : w ∉ failed S F l (flip x {((w,c),a)}) v := by
    intro hn
    have hsub : failed S F l x v ⊆ failed S F l (flip x {((w,c),a)}) v := by
      intro z hz
      rcases Finset.mem_insert.mp (hsubset hz) with hzw | hh
      · exact hzw ▸ hn
      · exact hh
    exact (Nat.not_le_of_lt hdec) (Finset.card_le_card hsub)
  rcases (Finset.mem_filter.mp hwold).2 with ⟨hR,htrue⟩
  have hl : S.label v w = c := by
    by_contra hn
    have hp : (w,S.label v w) ≠ (w,c) := fun h => hn (congrArg Prod.snd h)
    exact hwnew ((failed_flip_mem_other S F l x v w w c a hp).2 hwold)
  have hfalse : F (S.guard l) (flip (child x w c) {a}) = false := by
    cases hh : F (S.guard l) (flip (child x w c) {a}) with
    | false => rfl
    | true =>
        apply False.elim
        apply hwnew
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,hR,by simpa only [hl,child_flip_same] using hh⟩
  exact ⟨hR,hl,by simpa only [hl] using htrue,hfalse,by omega⟩

theorem parent_false_rejects_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (hx : parent S F l x = false)
    (v : V) (hq : (failed S F l x v).card ≤ S.tolerance l) :
    S.target l (failed S F l x v).card (child x v false) (child x v true) = false := by
  cases ht : S.target l (failed S F l x v).card (child x v false) (child x v true) with
  | false => rfl
  | true =>
      have hon := (parent_true_iff S F l x).2 ⟨v,hq,ht⟩
      rw [hx] at hon
      contradiction

variable [Preorder L]

/-- Every successful one-bit repair of a rejected graded parent is one of the
    actual target or guard candidates used by the q2 enumeration. -/
theorem graded_repair_detailed_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : ℕ → L) (l : L) (ht : Monotone t)
    (hgraded : ∀ d u z, S.target l d u z = (F (t d) u && F (t d) z))
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : parent S F l x = false)
    (hon : parent S F l (flip x {((w,c),a)}) = true) :
    ∃ v b, (w = v ∧ Q2CandidateTypes.TargetCandidate (fun k z => F (t k) z = true)
        (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true) ∧
        F (t b) (flip (child x w c) {a}) = true) ∨
      (Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
        (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true) ∧
        S.Adj v w ∧ S.label v w = c ∧ F (S.guard l) (child x w c) = true ∧
        F (S.guard l) (flip (child x w c) {a}) = false) := by
  obtain ⟨v,hq,hwin⟩ := (parent_true_iff S F l _).1 hon
  by_cases hw : w = v
  · subst w
    rw [failed_flip_own] at hq hwin
    let b := (failed S F l x v).card
    have hf := parent_false_rejects_row S F l x hoff v hq
    rw [hgraded] at hf hwin
    have hafterOwn : F (t b) (flip (child x v c) {a}) = true := by
      have hp : F (t b) (child (flip x {((v,c),a)}) v false) = true ∧
          F (t b) (child (flip x {((v,c),a)}) v true) = true := by simpa using hwin
      cases c
      · simpa only [child_flip_same] using hp.1
      · simpa only [child_flip_same] using hp.2
    refine ⟨v,b,Or.inl ⟨rfl,⟨hq,rfl,?_⟩,hafterOwn⟩⟩
    cases c
    · have hp : (v,true) ≠ (v,false) := by simp
      rw [child_flip_other x v v false true a hp] at hwin
      have hpartner : F (t b) (child x v true) = true := by
        have hh : F (t b) (child (flip x {((v,false),a)}) v false) = true ∧
            F (t b) (child x v true) = true := by simpa using hwin
        exact hh.2
      left
      refine ⟨?_,hpartner⟩
      intro hbad
      have he : (F (t b) (child x v false) && F (t b) (child x v true)) = true := by
        simp only [hbad,hpartner,Bool.and_self]
      rw [show b = (failed S F l x v).card from rfl, hf] at he
      contradiction
    · have hp : (v,false) ≠ (v,true) := by simp
      rw [child_flip_other x v v true false a hp] at hwin
      have hpartner : F (t b) (child x v false) = true := by
        have hh : F (t b) (child x v false) = true ∧
            F (t b) (child (flip x {((v,true),a)}) v true) = true := by simpa using hwin
        exact hh.1
      right
      refine ⟨hpartner,?_⟩
      intro hbad
      have he : (F (t b) (child x v false) && F (t b) (child x v true)) = true := by
        simp only [hbad,hpartner,Bool.and_self]
      rw [show b = (failed S F l x v).card from rfl, hf] at he
      contradiction
  · have hchild : ∀ e : Bool, child (flip x {((w,c),a)}) v e = child x v e := by
      intro e
      exact child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)
    rw [hchild false,hchild true,hgraded] at hwin
    let b := (failed S F l (flip x {((w,c),a)}) v).card
    have hpair : F (t b) (child x v false) = true ∧ F (t b) (child x v true) = true := by
      simpa using hwin
    have hdec : b < (failed S F l x v).card := by
      by_contra hn
      have hcount : (failed S F l x v).card ≤ b := Nat.le_of_not_gt hn
      have hweak0 := hF _ _ (ht hcount) _ hpair.1
      have hweak1 := hF _ _ (ht hcount) _ hpair.2
      have hrow : S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
        rw [hgraded]
        simp only [hweak0,hweak1,Bool.and_self]
      have hh := (parent_true_iff S F l x).2 ⟨v,hcount.trans hq,hrow⟩
      rw [hoff] at hh
      contradiction
    have hremove := failed_decrease S F l x v w c a hdec
    exact ⟨v,b,Or.inr ⟨⟨hq,hremove.2.2.2.2,hpair.1,hpair.2⟩,
      hremove.1,hremove.2.1,hremove.2.2.1,hremove.2.2.2.1⟩⟩

theorem graded_repair_candidate_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : ℕ → L) (l : L) (ht : Monotone t)
    (hgraded : ∀ d u z, S.target l d u z = (F (t d) u && F (t d) z))
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : parent S F l x = false)
    (hon : parent S F l (flip x {((w,c),a)}) = true) :
    ∃ v b, Q2CandidateTypes.TargetCandidate (fun k z => F (t k) z = true)
        (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true) ∨
      Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
        (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true) := by
  obtain ⟨v,b,h⟩ := graded_repair_detailed_cover S F hF t l ht hgraded x w c a hoff hon
  exact ⟨v,b,h.elim (fun ht => Or.inl ht.2.1) (fun hg => Or.inr hg.1)⟩

end
end ThreeBoundRepair

#print axioms ThreeBoundRepair.failed_decrease
#print axioms ThreeBoundRepair.graded_repair_detailed_cover
#print axioms ThreeBoundRepair.graded_repair_candidate_cover


