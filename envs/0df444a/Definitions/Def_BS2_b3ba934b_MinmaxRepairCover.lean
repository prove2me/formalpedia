-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRepairCover
-- name    : BS2_b3ba934b_MinmaxRepairCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:37:28.713053+00:00
-- url     : https://prove2.me/theorems/4e0702e8-5854-4683-9918-9e9ee655dfbc
-- title:
--   Sensitivity separation: MinmaxRepairCover (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRepairCover` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRepairCover.lean; original SHA-256 f5c1c8ffa2639def8181c2125ef61355963d74899e4651db0d891049d7ee942d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Every actual min/max parent repair is covered by an exact target repair
or the removal of one selected failed guard. -/
import Definitions.Def_BS2_b3ba934b_MinmaxCandidates

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem repair_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : parent S F j x=false) (hon : parent S F j (flip x {((w,c),a)})=true) :
    (∃ b, TargetCandidate S F P.strongLower P.strongUpper j x w b ∧
      a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x w) c) ∨
    (∃ v b, GuardCandidate S F P.strongLower P.strongUpper j x v b ∧
      S.Adj v w ∧ S.label v w=c ∧ F (S.guard j) (child x w c)=true ∧
        a ∈ flipsTo (F (S.guard j)) false (child x w c)) := by
  obtain ⟨v,hq,hwin⟩ := (parent_true_iff S F j _).1 hon
  by_cases hw : w=v
  · subst w
    rw [failed_flip_own] at hq hwin
    let b := (failed S F j x v).card
    have hf := parent_false_rejects_row S F j x hoff v hq
    rw [P.strongDef] at hf hwin
    have ha : a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x v) c := by
      cases c
      · rw [child_flip_same,child_flip_other x v v false true a (by simp)] at hwin
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwin⟩
      · rw [child_flip_other x v v true false a (by simp),child_flip_same,mm_comm] at hwin
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwin⟩
    have hp : F (P.strongLower b) (child x v false)=true ∨
        F (P.strongLower b) (child x v true)=true := by
      have hh := ((mm_true F _ _ _ _).1 (Finset.mem_filter.mp ha).2).2.1
      cases c
      · exact Or.inr hh
      · exact Or.inl hh
    exact Or.inl ⟨b,⟨hq,rfl,hf,hp⟩,ha⟩
  · have hchild : ∀ e : Bool, child (flip x {((w,c),a)}) v e=child x v e := by
      intro e
      exact child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)
    rw [hchild false,hchild true,P.strongDef] at hwin
    let b := (failed S F j (flip x {((w,c),a)}) v).card
    have hdec : b < (failed S F j x v).card := by
      by_contra hn
      have hc : (failed S F j x v).card ≤ b := Nat.le_of_not_gt hn
      have he := parent_true_of_count S F hF j P.strongLower P.strongUpper
        P.strongLowerMono P.strongUpperMono P.strongDef x v b hq hc hwin
      rw [hoff] at he
      contradiction
    obtain ⟨hR,hl,hbefore,hafter,hcount⟩ := failed_decrease S F j x v w c a hdec
    exact Or.inr ⟨v,b,⟨hq,hcount,hwin⟩,hR,hl,hbefore,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hafter⟩⟩

theorem actual_high_tags (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) (hq : S.tolerance j ≤ q) :
    ∃ tag : V → ThreeBoundHighTypes.Kind q,
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        ThreeBoundHighTypes.OfKind q
          (PositiveCandidate S F P.strongLower P.strongUpper j x w)
          (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) ∧
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        (failed S F j x w).card=ThreeBoundHighTypes.budget q (tag w)) ∧
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        ((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj w)).card ≤
          ThreeBoundHighTypes.budget q (tag w)) := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  have hex : ∀ w ∈ H, ∃ kind : ThreeBoundHighTypes.Kind q,
      ThreeBoundHighTypes.OfKind q (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) kind := by
    intro w hw
    exact ThreeBoundHighTypes.exists_kind q (failed S F j x w).card _ _
      (fun b hb => ⟨hb.1.1.trans hq,hb.1.2.1⟩)
      (fun b hb => ⟨hb.1.trans hq,hb.2.1⟩) (Finset.mem_filter.mp hw).2
  let tag : V → ThreeBoundHighTypes.Kind q := fun w =>
    if hw : w ∈ H then Classical.choose (hex w hw) else ⟨0,by omega⟩
  have hk : ∀ w ∈ H, ThreeBoundHighTypes.OfKind q
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w) := by
    intro w hw
    simpa only [tag,dif_pos hw] using Classical.choose_spec (hex w hw)
  have hc : ∀ w ∈ H, (failed S F j x w).card=ThreeBoundHighTypes.budget q (tag w) := by
    intro w hw
    exact ThreeBoundHighTypes.ofKind_count q (failed S F j x w).card _ _ (tag w)
      (fun b hb => hb.1.2.1) (fun b hb => hb.2.1) (hk w hw)
  refine ⟨tag,hk,hc,?_⟩
  intro w hw
  rw [← hc w hw]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvH,hR⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,
    high_guards_true S F hF i j P x v hvH (S.label w v)⟩

end
end ThreeBoundMinmaxCandidates

#print axioms ThreeBoundMinmaxCandidates.repair_cover
#print axioms ThreeBoundMinmaxCandidates.actual_high_tags


