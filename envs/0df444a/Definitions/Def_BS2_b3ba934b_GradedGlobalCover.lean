-- Prove2me | Definitions.Def_BS2_b3ba934b_GradedGlobalCover
-- name    : BS2_b3ba934b_GradedGlobalCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:07:33.879981+00:00
-- url     : https://prove2.me/theorems/2100401d-d58e-497f-b2bc-4a2c1f5b84de
-- title:
--   Sensitivity separation: GradedGlobalCover (complete source module)
-- statement:
--   Complete Lean source module `GradedGlobalCover` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GradedGlobalCover.lean; original SHA-256 bb5bcba294b60d2080cea6152e5a8ed3e393101f50bb6829c5883a2fa0c78f46; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual upward flips grouped into negative targets, high heads and external
   failed-guard arcs. Internal arcs are deduplicated by their selected child. -/
import Definitions.Def_BS2_b3ba934b_GradedPositionCover

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def targetAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  Q2CandidateTypes.TargetCandidate (fun b z => F (t b) z = true)
    (S.tolerance l) (failed S F l x v).card (failed S F l x v).card
      (child x v false) (child x v true)

def guardAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  ∃ b, Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
    (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true)

def highAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  Q2CandidateTypes.High (fun z => F (S.guard l) z = true)
    (fun b z => F (t b) z = true) (S.tolerance l) (failed S F l x v).card
      (child x v false) (child x v true)

def highHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter (highAt S F t l x)

def guardSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter (guardAt S F t l x)

def negativeTargets (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter fun v => targetAt S F t l x v ∧ ¬ highAt S F t l x v

def missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Bool :=
  if F (t (failed S F l x v).card) (child x v false) = true then true else false

def incomingSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset V :=
  (guardSources S F t l x).filter fun v => S.Adj v w

def hitChildren (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset Bool :=
  (incomingSources S F t l x w).image fun v => S.label v w

theorem hitChildren_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    (hitChildren S F t l x w).card ≤ (incomingSources S F t l x w).card :=
  Finset.card_image_le

def actualHeadParts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Finset I :=
  (if targetAt S F t l x w ∧ c = missing S F t l x w then
    flipsTo (F (t (failed S F l x w).card)) true (child x w c) else ∅) ∪
  (if c ∈ hitChildren S F t l x w then flipsTo (F (S.guard l)) false (child x w c) else ∅)

def highBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (highHeads S F t l x).biUnion fun w => headBits w (actualHeadParts S F t l x w)

def negativeBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (negativeTargets S F t l x).biUnion fun w => liftBits w (missing S F t l x w)
    (flipsTo (F (t (failed S F l x w).card)) true (child x w (missing S F t l x w)))

def externalBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (guardSources S F t l x).biUnion fun v =>
    (failed S F l x v \ highHeads S F t l x).biUnion fun w =>
      liftBits w (S.label v w)
        (flipsTo (F (S.guard l)) false (child x w (S.label v w)))

theorem target_missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V)
    (hc : targetAt S F t l x w) :
    F (t (failed S F l x w).card) (child x w (missing S F t l x w)) = false ∧
    F (t (failed S F l x w).card) (child x w (!(missing S F t l x w))) = true := by
  rcases hc.2.2 with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simp [missing,h0,Bool.eq_false_iff.mpr h0,h1]
  · simp [missing,h0,Bool.eq_false_iff.mpr h1]

theorem false_child_eq_missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool)
    (hc : targetAt S F t l x w)
    (hf : F (t (failed S F l x w).card) (child x w c) = false) :
    c = missing S F t l x w := by
  have hs := target_missing S F t l x w hc
  cases c <;> cases hm : missing S F t l x w <;> simp_all

/-- All actual parent repairs lie in precisely the three geometric charging
    classes. Each internal incoming arc contributes only its selected child. -/
theorem upward_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (t : ℕ → L) (l : L) (ht : Monotone t)
    (hgraded : ∀ d u z, S.target l d u z = (F (t d) u && F (t d) z))
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F l x = false) :
    flipsTo (parent S F l) true x ⊆
      (negativeBits S F t l x ∪ highBits S F t l x) ∪ externalBits S F t l x := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (Finset.mem_filter.mp ha).2
  rcases graded_repair_position_cover S F hF t l ht hgraded x w c a hoff hon with
    ⟨b,hcan,hbefore,hafter⟩ | ⟨v,b,hcan,hR,hl,hguard,hafter⟩
  · have hc : targetAt S F t l x w := by
      have he := hcan.2.1
      simpa only [targetAt,he] using hcan
    have hbefore' : F (t (failed S F l x w).card) (child x w c) = false := by
      simpa only [hcan.2.1] using hbefore
    have hafter' : a ∈ flipsTo (F (t (failed S F l x w).card)) true (child x w c) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa only [hcan.2.1] using hafter⟩
    have hcm := false_child_eq_missing S F t l x w c hc hbefore'
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    by_cases hh : highAt S F t l x w
    · right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩,?_⟩
      apply (mem_headBits w w _ c a).mpr
      refine ⟨rfl,Finset.mem_union.mpr (Or.inl ?_)⟩
      simpa only [if_pos (And.intro hc hcm)] using hafter'
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hh⟩,?_⟩
      apply (mem_liftBits w w _ c a _).mpr
      exact ⟨rfl,hcm,by simpa only [← hcm] using hafter'⟩
  · have hv : v ∈ guardSources S F t l x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨b,hcan⟩⟩
    have hw : w ∈ failed S F l x v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,by simpa only [hl] using hguard⟩
    have hb : a ∈ flipsTo (F (S.guard l)) false (child x w c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hafter⟩
    by_cases hh : w ∈ highHeads S F t l x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hh,(mem_headBits w w _ c a).mpr ⟨rfl,?_⟩⟩
      have hhit : c ∈ hitChildren S F t l x w :=
        Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hR⟩,hl⟩
      exact Finset.mem_union.mpr (Or.inr (by simpa only [if_pos hhit] using hb))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨v,hv,Finset.mem_biUnion.mpr ⟨w,Finset.mem_sdiff.mpr ⟨hw,hh⟩,?_⟩⟩
      apply (mem_liftBits w w _ c a _).mpr
      exact ⟨rfl,hl.symm,by simpa only [hl] using hb⟩

end
end ThreeBoundGradedCover

#print axioms ThreeBoundGradedCover.upward_subset
#print axioms ThreeBoundGradedCover.hitChildren_card_le


