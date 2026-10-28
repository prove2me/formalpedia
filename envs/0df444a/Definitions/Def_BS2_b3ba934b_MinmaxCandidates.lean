-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxCandidates
-- name    : BS2_b3ba934b_MinmaxCandidates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:35:50.061619+00:00
-- url     : https://prove2.me/theorems/947d74b5-c2b6-4ab0-a21e-8d4da55f9ce3
-- title:
--   Sensitivity separation: MinmaxCandidates (complete source module)
-- statement:
--   Complete Lean source module `MinmaxCandidates` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxCandidates.lean; original SHA-256 9619be3d44bb3c569599021722b9909bca5b60dba5926e8975b63088c223e5fa; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual geometric target and guard candidates for monotone min/max rows. -/
import Definitions.Def_BS2_b3ba934b_MinmaxHeadLocal
import Definitions.Def_BS2_b3ba934b_HighTypeCore
import Definitions.Def_BS2_b3ba934b_GradedRepairCover

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def TargetCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ) : Prop :=
  b ≤ S.tolerance j ∧ (failed S F j x w).card=b ∧
    mm F (t b) (u b) (child x w false) (child x w true)=false ∧
    (F (t b) (child x w false)=true ∨ F (t b) (child x w true)=true)

def PositiveCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ) : Prop :=
  TargetCandidate S F t u j x w b ∧ ∀ c, F (S.guard j) (child x w c)=true

def GuardCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ) : Prop :=
  b ≤ S.tolerance j ∧ (failed S F j x w).card=b+1 ∧
    mm F (t b) (u b) (child x w false) (child x w true)=true

def High (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) : Prop :=
  (∃ b, PositiveCandidate S F t u j x w b) ∨ ∃ b, GuardCandidate S F t u j x w b

def highHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter (High S F t u j x)

def guardSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter fun w => ∃ b, GuardCandidate S F t u j x w b

def targetPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) : Finset V :=
  Finset.univ.filter fun w => ∃ b, b ≤ q ∧ TargetCandidate S F t u j x w b

def negativeTargets (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  targetPrefix S F t u j x (S.tolerance j) \ highHeads S F t u j x

def missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (w : V) : Bool :=
  if F (S.guard j) (child x w false)=true then true else false

theorem high_guards_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x) :
    ∀ c, F (S.guard j) (child x w c)=true := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · have hh := (mm_true F _ _ _ _).1 hb.2.2
    intro c
    cases c
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.1
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.2.1

theorem target_some_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b) :
    F (S.guard j) (child x w false)=true ∨ F (S.guard j) (child x w true)=true :=
  hb.2.2.2.elim (fun hh => Or.inl (hF _ _ (P.guardTarget b hb.1) _ hh))
    (fun hh => Or.inr (hF _ _ (P.guardTarget b hb.1) _ hh))

theorem target_partner_guard (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b)
    (c : Bool) (hc : c ≠ missing S F j x w) : F (S.guard j) (child x w c)=true := by
  have hh := target_some_guard S F hF i j P x w b hb
  unfold missing at hc
  cases c <;> split_ifs at hc with he <;> simp_all

theorem negative_guard_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ negativeTargets S F P.strongLower P.strongUpper j x) :
    F (S.guard j) (child x w (missing S F j x w))=false := by
  obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨b,hb,hcan⟩ := (Finset.mem_filter.mp ht).2
  have hnot : ¬ ∀ c, F (S.guard j) (child x w c)=true := by
    intro hh
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨b,hcan,hh⟩⟩)
  have hsome := target_some_guard S F hF i j P x w b hcan
  unfold missing
  split_ifs with h0
  · apply Bool.eq_false_iff.mpr
    intro h1
    apply hnot
    intro c
    cases c <;> assumption
  · exact Bool.eq_false_iff.mpr h0

theorem weak_target_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (b : ℕ) (hb : b ≤ S.tolerance j)
    (hcount : (failed S F j x w).card ≤ b) :
    mm F (P.weakLower b) (P.weakUpper b) (child x w false) (child x w true)=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hc := (Finset.card_le_card (failed_weak_subset S F hF i j P x w)).trans hcount
  have he := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
    P.weakDef x w b (hb.trans P.tolerances) hc hh
  rw [hoff] at he
  contradiction

theorem guard_failures_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x w b) :
    failed S F i x w=failed S F j x w := by
  have hs := failed_weak_subset S F hF i j P x w
  have hle := Finset.card_le_card hs
  have hnot : ¬ (failed S F i x w).card ≤ b := by
    intro hc
    have hmm := mm_mono F hF _ _ _ _ (P.lowerOrder b hb.1) (P.upperOrder b hb.1) _ _ hb.2.2
    have he := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
      P.weakDef x w b (hb.1.trans P.tolerances) hc hmm
    rw [hoff] at he
    contradiction
  apply Finset.eq_of_subset_of_card_le hs
  have hd := hb.2.1
  omega

theorem guard_hit_eligible (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (v : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x v b)
    (w : V) (hw : w ∈ failed S F j x v) : F (S.guard i) (child x w (S.label v w))=true := by
  rw [← guard_failures_eq S F hF i j P x hoff v b hb] at hw
  exact (Finset.mem_filter.mp hw).2.2

theorem guard_forbidden_next (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x=false) (w : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x w b)
    (hq : b+1 ≤ S.tolerance i) (ht : P.weakLower (b+1) ≤ P.strongLower b)
    (hu : P.weakUpper (b+1) ≤ P.strongUpper b) : False := by
  have hc := Finset.card_le_card (failed_weak_subset S F hF i j P x w)
  rw [hb.2.1] at hc
  have hmm := mm_mono F hF _ _ _ _ ht hu _ _ hb.2.2
  have he := parent_true_of_count S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
    P.weakDef x w (b+1) hq hc hmm
  rw [hoff] at he
  contradiction

end
end ThreeBoundMinmaxCandidates

#print axioms ThreeBoundMinmaxCandidates.high_guards_true
#print axioms ThreeBoundMinmaxCandidates.guard_failures_eq
#print axioms ThreeBoundMinmaxCandidates.guard_forbidden_next


