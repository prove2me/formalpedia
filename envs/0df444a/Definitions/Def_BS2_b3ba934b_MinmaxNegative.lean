-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxNegative
-- name    : BS2_b3ba934b_MinmaxNegative
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:43:52.596492+00:00
-- url     : https://prove2.me/theorems/654c39e9-92c0-4407-ad1b-11e0b906ec0b
-- title:
--   Sensitivity separation: MinmaxNegative (complete source module)
-- statement:
--   Complete Lean source module `MinmaxNegative` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxNegative.lean; original SHA-256 b45c6828f2a8d4241d91ca1335472200d969e06214629ec27ad2e1b2454177ac; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Negative target repairs and cumulative tier allocation for min/max. -/
import Definitions.Def_BS2_b3ba934b_MinmaxGlobalCover
import Definitions.Def_BS2_b3ba934b_MinmaxRecordCaps
import Definitions.Def_BS2_b3ba934b_MinmaxAExpressions
import Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch
import Definitions.Def_BS2_b3ba934b_NegativeGreedy
import Definitions.Def_BS2_b3ba934b_NumericOrderBounds

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mem_targetPrefix_iff (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) (w : V) :
    w ∈ targetPrefix S F t u j x q ↔
      targetAt S F t u j x w ∧ (failed S F j x w).card ≤ q := by
  simp only [targetPrefix,Finset.mem_filter,Finset.mem_univ,true_and,targetAt]
  constructor
  · rintro ⟨b,hb,ht⟩
    exact ⟨⟨b,ht⟩,ht.2.1.le.trans hb⟩
  · rintro ⟨⟨b,ht⟩,hc⟩
    exact ⟨b,by rw [← ht.2.1]; exact hc,ht⟩

def negativeTier (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (b : ℕ) : Finset V :=
  (negativeTargets S F t u j x).filter fun w => (failed S F j x w).card=b

theorem negative_prefix_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (negativeTargets S F t u j x).filter (fun v => (failed S F j x v).card ≤ q) =
      targetPrefix S F t u j x q \ highHeads S F t u j x := by
  ext w
  simp only [negativeTargets,Finset.mem_filter,Finset.mem_sdiff,mem_targetPrefix_iff]
  constructor
  · tauto
  · rintro ⟨⟨ht,hq⟩,hh⟩
    obtain ⟨b,hb⟩ := ht
    exact ⟨⟨⟨⟨b,hb⟩,hb.2.1.le.trans hb.1⟩,hh⟩,hq⟩

theorem negative_prefix_sum (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (∑ b ∈ Finset.range (q+1), (negativeTier S F t u j x b).card) =
      (targetPrefix S F t u j x q \ highHeads S F t u j x).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (negativeTargets S F t u j x)
    (Finset.range (q+1)) (fun v => (failed S F j x v).card)
  simp only [Finset.mem_range,Nat.lt_succ_iff] at h
  simpa only [negativeTier,negative_prefix_eq] using h

theorem negative_prefix_after_positive (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q cap : ℕ)
    (hcap : (targetPrefix S F t u j x q).card ≤ cap) :
    (∑ b ∈ Finset.range (q+1), (negativeTier S F t u j x b).card) ≤
      cap-(targetPrefix S F t u j x q ∩ highHeads S F t u j x).card := by
  rw [negative_prefix_sum]
  have h := Finset.card_sdiff_add_card_inter (targetPrefix S F t u j x q) (highHeads S F t u j x)
  omega

theorem negativeBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (b : ℕ → ℕ)
    (hb : ∀ k, k ≤ S.tolerance j → ABound F (S.guard j) (P.strongLower k) (b k)) :
    (negativeBits S F P.strongLower P.strongUpper j x).card ≤
      ∑ k ∈ Finset.range (S.tolerance j+1),
        (negativeTier S F P.strongLower P.strongUpper j x k).card*b k := by
  have hm : ∀ v ∈ negativeTargets S F P.strongLower P.strongUpper j x,
      (failed S F j x v).card ∈ Finset.range (S.tolerance j+1) := by
    intro v hv
    have ht := (mem_targetPrefix_iff S F P.strongLower P.strongUpper j x _ v).1
      (Finset.mem_sdiff.mp hv).1
    exact Finset.mem_range.mpr (by omega)
  have hg := Finset.sum_fiberwise_of_maps_to'
    (s := negativeTargets S F P.strongLower P.strongUpper j x)
    (t := Finset.range (S.tolerance j+1)) (g := fun v => (failed S F j x v).card) hm b
  have hg' : (∑ k ∈ Finset.range (S.tolerance j+1),
      (negativeTier S F P.strongLower P.strongUpper j x k).card*b k) =
      ∑ v ∈ negativeTargets S F P.strongLower P.strongUpper j x, b (failed S F j x v).card := by
    simpa [negativeTier,Finset.sum_const,nsmul_eq_mul] using hg
  rw [hg']
  unfold negativeBits
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro v hv
  rw [card_liftBits]
  exact hb _ (Nat.le_of_lt_succ (Finset.mem_range.mp (hm v hv))) _
    (negative_guard_false S F hF i j P x v hv)

end
end ThreeBoundMinmaxCover

#print axioms ThreeBoundMinmaxCover.negativeBits_card_le


