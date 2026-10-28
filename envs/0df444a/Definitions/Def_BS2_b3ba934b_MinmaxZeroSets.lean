-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroSets
-- name    : BS2_b3ba934b_MinmaxZeroSets
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:40:54.337339+00:00
-- url     : https://prove2.me/theorems/f0927e9f-0ec3-4f32-a16e-72422d86ed3e
-- title:
--   Sensitivity separation: MinmaxZeroSets (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroSets` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroSets.lean; original SHA-256 813de7d6b633d4fa3325c43999b5e309a62b9c50fa6bd794576caa43e3b6468d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The actual candidate geometry at strong tolerance zero. -/
import Definitions.Def_BS2_b3ba934b_MinmaxPrefixCaps
import Definitions.Def_BS2_b3ba934b_MinmaxGlobalCover
import Definitions.Def_BS2_b3ba934b_ZeroGeometry

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroSets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates
open TournamentHighRows CandidateCoherence ResidualCaps ThreeBoundZeroGeometry
open ThreeBoundActualEnumeration (guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def targets (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter fun w => TargetCandidate S F t u j x w 0

def positives (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter fun w => PositiveCandidate S F t u j x w 0

theorem mem_targets (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    w∈targets S F t u j x ↔ TargetCandidate S F t u j x w 0 := by
  simp only [targets,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_positives (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    w∈positives S F t u j x ↔ PositiveCandidate S F t u j x w 0 := by
  simp only [positives,Finset.mem_filter,Finset.mem_univ,true_and]

theorem guards_iff (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (w : V) :
    w∈guardSources S F t u j x ↔ GuardCandidate S F t u j x w 0 := by
  constructor
  · intro hw
    obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hw).2
    have he : b=0 := by have := hb.1; omega
    simpa only [he] using hb
  · intro hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,hw⟩

theorem targets_prefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) :
    targets S F t u j x=targetPrefix S F t u j x 0 := by
  ext w
  rw [mem_targets]
  constructor
  · intro hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,le_refl 0,hw⟩
  · intro hw
    obtain ⟨b,hb,hcan⟩ := (Finset.mem_filter.mp hw).2
    have he : b=0 := Nat.eq_zero_of_le_zero hb
    simpa only [he] using hcan

theorem positive_subset_target (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) :
    positives S F t u j x⊆targets S F t u j x := by
  intro w hw
  exact (mem_targets _ _ _ _ _ _ _).mpr ((mem_positives _ _ _ _ _ _ _).mp hw).1

theorem target_guard_disjoint (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    Disjoint (targets S F t u j x) (guardSources S F t u j x) := by
  apply Finset.disjoint_left.mpr
  intro w hw hg
  have ht := ((mem_targets _ _ _ _ _ _ _).mp hw).2.1
  have hguard := ((guards_iff _ _ _ _ _ hq _ _).mp hg).2.1
  omega

theorem high_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    highHeads S F t u j x=positives S F t u j x∪guardSources S F t u j x := by
  ext w
  simp only [highHeads,Finset.mem_filter,Finset.mem_univ,true_and,High,Finset.mem_union]
  constructor
  · rintro (⟨b,hb⟩ | hg)
    · have he : b=0 := by have := hb.1.1; omega
      exact Or.inl ((mem_positives _ _ _ _ _ _ _).mpr (by simpa only [he] using hb))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩)
  · rintro (hp | hg)
    · exact Or.inl ⟨0,(mem_positives _ _ _ _ _ _ _).mp hp⟩
    · exact Or.inr (Finset.mem_filter.mp hg).2

theorem negative_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    negativeTargets S F t u j x=targets S F t u j x\positives S F t u j x := by
  rw [negativeTargets,hq,← targets_prefix,high_eq S F t u j hq]
  ext w
  simp only [Finset.mem_sdiff,Finset.mem_union,not_or]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · intro h
    exact ⟨h.1,h.2,fun hg => Finset.disjoint_left.mp (target_guard_disjoint S F t u j hq x) h.1 hg⟩

theorem negative_target (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hw : w∈negativeTargets S F t u j x) : TargetCandidate S F t u j x w 0 := by
  rw [negative_eq S F t u j hq] at hw
  exact (mem_targets _ _ _ _ _ _ _).mp (Finset.mem_sdiff.mp hw).1

theorem negative_disjoint_high (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) :
    Disjoint (negativeTargets S F t u j x) (highHeads S F t u j x) := by
  exact Finset.sdiff_disjoint

theorem high_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    (highHeads S F t u j x).card=(positives S F t u j x).card+(guardSources S F t u j x).card := by
  rw [high_eq S F t u j hq]
  exact Finset.card_union_of_disjoint ((target_guard_disjoint S F t u j hq x).mono_left
    (positive_subset_target S F t u j x))

theorem target_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    (negativeTargets S F t u j x).card+(positives S F t u j x).card=(targets S F t u j x).card := by
  rw [negative_eq S F t u j hq]
  exact Finset.card_sdiff_add_card_eq_card (positive_subset_target S F t u j x)

theorem high_failure_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (w : V) (hw : w∈highHeads S F t u j x) :
    (failed S F j x w).card=if w∈guardSources S F t u j x then 1 else 0 := by
  by_cases hg : w∈guardSources S F t u j x
  · rw [if_pos hg]
    exact ((guards_iff S F t u j hq x w).mp hg).2.1
  · rw [if_neg hg]
    rw [high_eq S F t u j hq] at hw
    exact ((mem_positives _ _ _ _ _ _ _).mp ((Finset.mem_union.mp hw).resolve_right hg)).1.2.1

theorem positive_card_le_one (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (t u : ℕ → L) (j : L)
    (x : ((V × Bool) × I) → Bool) : (positives S F t u j x).card≤1 := by
  have hh := high_rows_card_le S.Adj hR S.label (fun z => F (S.guard j) z=true)
    (child x) (positives S F t u j x) 0
    (fun w hw => ((mem_positives _ _ _ _ _ _ _).mp hw).2) ?_
  · simpa only [Nat.mul_zero,Nat.zero_add] using hh
  · intro w hw
    rw [guardFailures_eq]
    exact ((mem_positives _ _ _ _ _ _ _).mp hw).1.2.1.le

theorem guard_card_le_three (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V × Bool) × I) → Bool) :
    (guardSources S F P.strongLower P.strongUpper j x).card≤3 := by
  have hh := high_rows_card_le S.Adj hR S.label (fun z => F (S.guard j) z=true)
    (child x) (guardSources S F P.strongLower P.strongUpper j x) 1 ?_ ?_
  · exact hh
  · intro w hw
    apply high_guards_true S F hF i j P x w
    rw [high_eq S F P.strongLower P.strongUpper j hq]
    exact Finset.mem_union_right _ hw
  · intro w hw
    rw [guardFailures_eq]
    exact ((guards_iff S F P.strongLower P.strongUpper j hq x w).mp hw).2.1.le

theorem target_cap (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (a : ℕ)
    (hcap : NoOrdinary S.Adj S.label 0 a) :
    (targets S F P.strongLower P.strongUpper j x).card≤a-1 := by
  have hg := ordinaryGood_of_actual_guards S.Adj S.label (fun z => F (S.guard j) z=true)
    (child x) (targets S F P.strongLower P.strongUpper j x) 0 (missing S F j x)
    (fun w hw c hc => target_partner_guard S F hF i j P x w 0
      ((mem_targets _ _ _ _ _ _ _).mp hw) c hc) ?_
  · have hh := ordinary_card_lt S.Adj S.label 0 a hcap _ _ hg
    omega
  · intro w hw
    rw [guardFailures_eq]
    exact ((mem_targets _ _ _ _ _ _ _).mp hw).2.1.le

def deleted (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  deletedHeads S.Adj S.label (negativeTargets S F t u j x) (highHeads S F t u j x) (missing S F j x)

theorem negative_cleaned_cap (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V × Bool) × I) → Bool) (m a : ℕ)
    (hm : m≤(highHeads S F P.strongLower P.strongUpper j x).card)
    (hcap : DominatorCardBound S.Adj S.label m a) :
    (negativeTargets S F P.strongLower P.strongUpper j x).card≤a-1+
      (deleted S F P.strongLower P.strongUpper j x).card := by
  apply cleaned_zero_cap S.Adj hR S.label (fun z => F (S.guard j) z=true) (child x)
    _ _ (negative_disjoint_high S F P.strongLower P.strongUpper j x) (missing S F j x) m a hm hcap
  · intro w hw c hc
    exact target_partner_guard S F hF i j P x w 0
      (negative_target S F P.strongLower P.strongUpper j hq x w hw) c hc
  · exact high_guards_true S F hF i j P x
  · intro w hw
    rw [guardFailures_eq]
    exact (negative_target S F P.strongLower P.strongUpper j hq x w hw).2.1

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.negative_cleaned_cap


