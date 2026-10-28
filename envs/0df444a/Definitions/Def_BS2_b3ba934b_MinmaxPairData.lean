-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxPairData
-- name    : BS2_b3ba934b_MinmaxPairData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:26:04.923995+00:00
-- url     : https://prove2.me/theorems/e2adb5b7-0434-483a-b739-64ae455020cc
-- title:
--   Sensitivity separation: MinmaxPairData (complete source module)
-- statement:
--   Complete Lean source module `MinmaxPairData` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxPairData.lean; original SHA-256 511d9bc3486874dcd0de87dbbfb9d3333f872f8f4bf822bb0615be959f22d647; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Shared actual-predicate interface for symmetric min/max transfer. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalBase
import Definitions.Def_BS2_b3ba934b_MinMaxNesting

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def mm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) : Bool :=
  F t x && F t y && (F u x || F u y)

theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]

theorem mm_comm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=mm F t u y x := by
  simp only [mm,Bool.and_comm,Bool.or_comm]

theorem mm_mono (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (ht : ti ≤ tj) (hu : ui ≤ uj) (x y : I → Bool)
    (h : mm F tj uj x y=true) : mm F ti ui x y=true := by
  rw [mm_true] at h ⊢
  exact ⟨hF _ _ ht _ h.1,hF _ _ ht _ h.2.1,
    h.2.2.elim (fun hh => Or.inl (hF _ _ hu _ hh)) (fun hh => Or.inr (hF _ _ hu _ hh))⟩

structure PairData (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) where
  weakLower : ℕ → L
  weakUpper : ℕ → L
  strongLower : ℕ → L
  strongUpper : ℕ → L
  weakLowerMono : Monotone weakLower
  weakUpperMono : Monotone weakUpper
  strongLowerMono : Monotone strongLower
  strongUpperMono : Monotone strongUpper
  weakLowerUpper : ∀ b, b ≤ S.tolerance i → weakLower b ≤ weakUpper b
  strongLowerUpper : ∀ b, b ≤ S.tolerance j → strongLower b ≤ strongUpper b
  guards : S.guard j ≤ S.guard i
  tolerances : S.tolerance j ≤ S.tolerance i
  lowerOrder : ∀ b, b ≤ S.tolerance j → weakLower b ≤ strongLower b
  upperOrder : ∀ b, b ≤ S.tolerance j → weakUpper b ≤ strongUpper b
  weakDef : ∀ d x y, S.target i d x y = mm F (weakLower d) (weakUpper d) x y
  strongDef : ∀ d x y, S.target j d x y = mm F (strongLower d) (strongUpper d) x y
  weakGuardTarget : ∀ b, b ≤ S.tolerance i → S.guard i ≤ weakLower b
  guardTarget : ∀ b, b ≤ S.tolerance j → S.guard j ≤ strongLower b

theorem parent_true_of_count (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : d ≤ S.tolerance l) (hc : (failed S F l x w).card ≤ d)
    (hm : mm F (t d) (u d) (child x w false) (child x w true)=true) : parent S F l x=true := by
  apply (parent_true_iff S F l x).2
  refine ⟨w,hc.trans hd,?_⟩
  rw [hdef]
  exact mm_mono F hF _ _ _ _ (ht hc) (hu hc) _ _ hm

theorem failed_weak_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) : failed S F i x w ⊆ failed S F j x w := by
  intro z hz
  obtain ⟨_,hR,htrue⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hF _ _ P.guards _ htrue⟩

theorem strong_false_of_weak_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hx : parent S F i x=false) : parent S F j x=false := by
  cases hh : parent S F j x with
  | false => rfl
  | true =>
      obtain ⟨w,hcount,hm⟩ := (parent_true_iff S F j x).1 hh
      rw [P.strongDef] at hm
      have hc := Finset.card_le_card (failed_weak_subset S F hF i j P x w)
      have ht := mm_mono F hF _ _ _ _ (P.lowerOrder _ hcount) (P.upperOrder _ hcount) _ _ hm
      have hon := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
        P.weakDef x w _ (hcount.trans P.tolerances) hc ht
      rw [hx] at hon
      contradiction

/-- Fixing which child supplies the upper threshold gives an actual component
of the symmetric parent at every safe upper bound on the failed-guard count. -/
theorem oriented_component_accepts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤ S.tolerance l → t b ≤ u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ) (c : Bool)
    (hd : d ≤ S.tolerance l) (hc : (failed S F l x w).card ≤ d)
    (hlow : F (t d) (child x w (!c))=true) (hhigh : F (u d) (child x w c)=true) :
    parent S F l x=true := by
  apply parent_true_of_count S F hF l t u ht hu hdef x w d hd hc
  have hlow' := hF _ _ (hlu d hd) _ hhigh
  cases c <;> simp_all only [Bool.not_false,Bool.not_true,mm_true,true_or,or_true,and_self]

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.parent_true_of_count
#print axioms ThreeBoundMinmaxTransfer.oriented_component_accepts


