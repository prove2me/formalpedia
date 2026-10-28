-- Prove2me | Definitions.Def_BS2_b3ba934b_GradedPositionCover
-- name    : BS2_b3ba934b_GradedPositionCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:06:59.354365+00:00
-- url     : https://prove2.me/theorems/60a05e8e-68d3-4bb2-8a54-722adadbe150
-- title:
--   Sensitivity separation: GradedPositionCover (complete source module)
-- statement:
--   Complete Lean source module `GradedPositionCover` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GradedPositionCover.lean; original SHA-256 bb0e739547b8a312f537cd0eea517f51df5d320c18f47f1c1f7899912b85323b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Position-resolved cover of actual upward flips of a graded parent. -/
import Definitions.Def_BS2_b3ba934b_GradedCandidates

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

/-- The target branch records that the actually changed child was false.
    This is needed to charge its bit to the uniquely missing child. -/
theorem graded_repair_position_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : ℕ → L) (l : L) (ht : Monotone t)
    (hgraded : ∀ d u z, S.target l d u z = (F (t d) u && F (t d) z))
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : parent S F l x = false)
    (hon : parent S F l (flip x {((w,c),a)}) = true) :
    (∃ b, Q2CandidateTypes.TargetCandidate (fun k z => F (t k) z = true)
        (S.tolerance l) (failed S F l x w).card b (child x w false) (child x w true) ∧
        F (t b) (child x w c) = false ∧ F (t b) (flip (child x w c) {a}) = true) ∨
      (∃ v b, Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
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
    have hpair : ∀ e, F (t b) (child (flip x {((v,c),a)}) v e) = true := by
      intro e
      have hh : F (t b) (child (flip x {((v,c),a)}) v false) = true ∧
          F (t b) (child (flip x {((v,c),a)}) v true) = true := by simpa using hwin
      cases e
      · exact hh.1
      · exact hh.2
    have hafter : F (t b) (flip (child x v c) {a}) = true := by
      simpa only [child_flip_same] using hpair c
    have hpartner : F (t b) (child x v (!c)) = true := by
      have hne : (v,!c) ≠ (v,c) := by cases c <;> simp
      simpa only [child_flip_other x v v c (!c) a hne] using hpair (!c)
    have hbefore : F (t b) (child x v c) = false := by
      cases hh : F (t b) (child x v c) with
      | false => rfl
      | true =>
          have both : (F (t b) (child x v false) && F (t b) (child x v true)) = true := by
            cases c <;> simp_all
          rw [show b = (failed S F l x v).card from rfl,hf] at both
          contradiction
    left
    refine ⟨b,⟨hq,rfl,?_⟩,hbefore,hafter⟩
    cases c
    · exact Or.inl ⟨by simpa [hbefore],hpartner⟩
    · exact Or.inr ⟨hpartner,by simpa [hbefore]⟩
  · right
    have hchild : ∀ e : Bool, child (flip x {((w,c),a)}) v e = child x v e := by
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
    exact ⟨v,b,⟨hq,hremove.2.2.2.2,hpair.1,hpair.2⟩,
      hremove.1,hremove.2.1,hremove.2.2.1,hremove.2.2.2.1⟩

end
end ThreeBoundGradedCover

#print axioms ThreeBoundGradedCover.graded_repair_position_cover


