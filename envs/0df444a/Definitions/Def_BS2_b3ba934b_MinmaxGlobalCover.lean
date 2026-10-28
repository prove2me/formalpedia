-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxGlobalCover
-- name    : BS2_b3ba934b_MinmaxGlobalCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:38:48.884073+00:00
-- url     : https://prove2.me/theorems/68b8f351-0c5b-443a-a08f-90598fbd4d1e
-- title:
--   Sensitivity separation: MinmaxGlobalCover (complete source module)
-- statement:
--   Complete Lean source module `MinmaxGlobalCover` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxGlobalCover.lean; original SHA-256 2d6d60c27bd5cf1f345e9a909d9e3cfee2350ff2121ec62912c1a9247b3d4ef4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Deduplicated actual repair sets for the min/max construction. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRepairCover
import Definitions.Def_BS2_b3ba934b_GlobalAccounting

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def targetAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) : Prop :=
  ∃ b, TargetCandidate S F t u j x w b

def targetParts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Finset I :=
  if targetAt S F t u j x w then
    upPart F (t (failed S F j x w).card) (u (failed S F j x w).card) (child x w) c else ∅

def hitChildren (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset Bool :=
  ThreeBoundAccounting.hits S.Adj S.label (guardSources S F t u j x) w

def incomingSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset V :=
  (guardSources S F t u j x).filter fun v => S.Adj v w

def actualHeadParts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Finset I :=
  targetParts S F t u j x w c ∪ guardParts F (S.guard j) (child x w) (hitChildren S F t u j x w) c

def highBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (highHeads S F t u j x).biUnion fun w => headBits w (actualHeadParts S F t u j x w)

def negativeBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (negativeTargets S F t u j x).biUnion fun w => liftBits w (missing S F j x w)
    (flipsTo (F (t (failed S F j x w).card)) true (child x w (missing S F j x w)))

def externalBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  ThreeBoundAccounting.externalBits S F j x (guardSources S F t u j x) (highHeads S F t u j x)

theorem negative_repair_missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ)
    (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b)
    (hw : w ∈ negativeTargets S F P.strongLower P.strongUpper j x)
    (c : Bool) (a : I) (ha : a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x w) c) :
    c=missing S F j x w := by
  have hh := ((mm_true F _ _ _ _).1 (Finset.mem_filter.mp ha).2).2.1
  have hg := hF _ _ (P.guardTarget b hb.1) _ hh
  have hf := negative_guard_false S F hF i j P x w hw
  by_contra hn
  have he : (!c)=missing S F j x w := by
    cases c <;> cases h : missing S F j x w <;> simp_all
  rw [he,hf] at hg
  contradiction

theorem upward_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F j x=false) :
    flipsTo (parent S F j) true x ⊆
      negativeBits S F P.strongLower P.strongUpper j x ∪
      highBits S F P.strongLower P.strongUpper j x ∪
      externalBits S F P.strongLower P.strongUpper j x := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (Finset.mem_filter.mp ha).2
  rcases repair_cover S F hF i j P x w c a hoff hon with
    ⟨b,hcan,hpart⟩ | ⟨v,b,hcan,hR,hl,hguard,hpart⟩
  · have ht : targetAt S F P.strongLower P.strongUpper j x w := ⟨b,hcan⟩
    have hpart' : a ∈ upPart F (P.strongLower (failed S F j x w).card)
        (P.strongUpper (failed S F j x w).card) (child x w) c := by
      simpa only [hcan.2.1] using hpart
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
    · right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hh,(mem_headBits w w _ c a).mpr ⟨rfl,?_⟩⟩
      exact Finset.mem_union.mpr (Or.inl (by simpa only [targetParts,if_pos ht] using hpart'))
    · left
      have hn : w ∈ negativeTargets S F P.strongLower P.strongUpper j x :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hcan.1,hcan⟩,hh⟩
      have hc := negative_repair_missing S F hF i j P x w b hcan hn c a hpart
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hn,(mem_liftBits w w _ c a _).mpr ⟨rfl,hc,?_⟩⟩
      rw [← hc]
      exact upPart_subset_lower F _ _ _ c hpart'
  · have hv : v ∈ guardSources S F P.strongLower P.strongUpper j x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hcan⟩
    have hw : w ∈ failed S F j x v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,by simpa only [hl] using hguard⟩
    by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hh,(mem_headBits w w _ c a).mpr ⟨rfl,?_⟩⟩
      have hhit : c ∈ hitChildren S F P.strongLower P.strongUpper j x w :=
        (ThreeBoundAccounting.mem_hits _ _ _ w c).mpr ⟨v,hv,hR,hl⟩
      exact Finset.mem_union.mpr (Or.inr (by simpa only [guardParts,if_pos hhit] using hpart))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨v,hv,Finset.mem_biUnion.mpr ⟨w,Finset.mem_sdiff.mpr ⟨hw,hh⟩,?_⟩⟩
      exact (mem_liftBits w w _ c a _).mpr ⟨rfl,hl.symm,by simpa only [hl] using hpart⟩

theorem head_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    (headBits w (actualHeadParts S F t u j x w)).card ≤
      (headBits w (targetParts S F t u j x w)).card+
      (headBits w (guardParts F (S.guard j) (child x w) (hitChildren S F t u j x w))).card := by
  have he : headBits w (actualHeadParts S F t u j x w) =
      headBits w (targetParts S F t u j x w) ∪
        headBits w (guardParts F (S.guard j) (child x w) (hitChildren S F t u j x w)) := by
    ext bit
    rcases bit with ⟨⟨v,c⟩,a⟩
    simp only [Finset.mem_union,mem_headBits,actualHeadParts]
    tauto
  rw [he]
  exact Finset.card_union_le _ _

end
end ThreeBoundMinmaxCover

#print axioms ThreeBoundMinmaxCover.upward_subset


