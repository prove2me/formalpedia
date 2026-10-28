-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualTargetAccounting
-- name    : BS2_b3ba934b_ActualTargetAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:29:10.369455+00:00
-- url     : https://prove2.me/theorems/0fc8e97d-b357-4a3c-9d55-49d2e37eeec6
-- title:
--   Sensitivity separation: ActualTargetAccounting (complete source module)
-- statement:
--   Complete Lean source module `ActualTargetAccounting` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualTargetAccounting.lean; original SHA-256 ad133c8c9a1c6d76f1d1211b907c87689cb8d2b17dd457c45348e335ce3f0ebe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual target candidate prefixes and their negative repair contribution. -/
import Definitions.Def_BS2_b3ba934b_ActualQ2Enumeration
import Definitions.Def_BS2_b3ba934b_ActualPrefixCaps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualTargets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundActualEnumeration ThreeBoundPrefixCaps
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def targetPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) : Finset V :=
  Finset.univ.filter fun v => targetAt S F t j x v ∧ (failed S F j x v).card ≤ q

def negativeTier (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (b : ℕ) : Finset V :=
  (negativeTargets S F t j x).filter fun v => (failed S F j x v).card = b

theorem nonmissing_partner (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (hw : targetAt S F P.strong j x w)
    (c : Bool) (hc : c ≠ missing S F P.strong j x w) :
    F (S.guard j) (child x w c) = true := by
  have hp := (target_missing S F P.strong j x w hw).2
  have he : c = !(missing S F P.strong j x w) := by
    cases c <;> cases hm : missing S F P.strong j x w <;> simp_all
  rw [he]
  exact hF _ _ (P.guardTarget _ hw.1) _ hp

theorem prefix_guard_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool)
    (q : ℕ) (v : V) (hv : v ∈ targetPrefix S F t j x q) :
    (TournamentHighRows.guardFailures S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) v).card ≤ q := by
  rw [guardFailures_eq]
  exact (Finset.mem_filter.mp hv).2.2

theorem actual_ordinary_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q a : ℕ)
    (hcap : CandidateCoherence.NoOrdinary S.Adj S.label q a) :
    let T := targetPrefix S F P.strong j x q
    let H := highHeads S F P.strong j x
    T.card ≤ min
      (a-1-((H \ T).filter fun v => (failed S F j x v).card ≤ q).card)
      (a-((H \ T).filter fun v => (failed S F j x v).card ≤ q+1).card) := by
  dsimp only
  have h := ordinary_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strong j x q) (highHeads S F P.strong j x)
    (missing S F P.strong j x) q a hcap
    (fun w hw c hc => nonmissing_partner S F hF i j P x w (Finset.mem_filter.mp hw).2.1 c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strong j x q)
  simpa only [outsideHigh,guardFailures_eq] using h

theorem actual_marked_prefix_cap (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤ ((highHeads S F P.strong j x).filter fun v => (failed S F j x v).card ≤ q+1).card)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m (m*(q+1)) a) :
    let T := targetPrefix S F P.strong j x q
    let H := highHeads S F P.strong j x
    T.card ≤ a-1+(m-((H \ T).filter fun v => (failed S F j x v).card ≤ q+1).card) := by
  dsimp only
  have hm' : m ≤ (eligibleHigh S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F P.strong j x) q).card := by
    simpa only [eligibleHigh,guardFailures_eq] using hm
  have h := marked_prefix_cap S.Adj S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strong j x q) (highHeads S F P.strong j x)
    (missing S F P.strong j x) q m a hm' hcap
    (fun w hw c hc => nonmissing_partner S F hF i j P x w (Finset.mem_filter.mp hw).2.1 c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strong j x q)
  simpa only [outsideHigh,guardFailures_eq] using h

theorem negative_prefix_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (negativeTargets S F t j x).filter (fun v => (failed S F j x v).card ≤ q) =
      targetPrefix S F t j x q \ highHeads S F t j x := by
  ext v
  simp only [negativeTargets,targetPrefix,highHeads,Finset.mem_filter,Finset.mem_sdiff,
    Finset.mem_univ,true_and]
  tauto

theorem negative_prefix_sum (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) :
    (∑ b ∈ Finset.range (q+1), (negativeTier S F t j x b).card) =
      (targetPrefix S F t j x q \ highHeads S F t j x).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (negativeTargets S F t j x)
    (Finset.range (q+1)) (fun v => (failed S F j x v).card)
  simp only [Finset.mem_range,Nat.lt_succ_iff] at h
  simpa only [negativeTier,negative_prefix_eq] using h

theorem negative_prefix_after_positive (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q cap : ℕ)
    (hcap : (targetPrefix S F t j x q).card ≤ cap) :
    (∑ b ∈ Finset.range (q+1), (negativeTier S F t j x b).card) ≤
      cap-(targetPrefix S F t j x q ∩ highHeads S F t j x).card := by
  rw [negative_prefix_sum]
  have h := Finset.card_sdiff_add_card_inter (targetPrefix S F t j x q) (highHeads S F t j x)
  omega

theorem negativeBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (b : ℕ → ℕ)
    (hb : ∀ k, k ≤ S.tolerance j → ABound F (S.guard j) (P.strong k) (b k)) :
    (negativeBits S F P.strong j x).card ≤
      ∑ k ∈ Finset.range (S.tolerance j+1), (negativeTier S F P.strong j x k).card*b k := by
  have hm : ∀ v ∈ negativeTargets S F P.strong j x,
      (failed S F j x v).card ∈ Finset.range (S.tolerance j+1) := by
    intro v hv
    have ht := (Finset.mem_filter.mp hv).2.1.1
    exact Finset.mem_range.mpr (by omega)
  have hg := Finset.sum_fiberwise_of_maps_to'
    (s := negativeTargets S F P.strong j x) (t := Finset.range (S.tolerance j+1))
    (g := fun v => (failed S F j x v).card) hm b
  have hg' : (∑ k ∈ Finset.range (S.tolerance j+1), (negativeTier S F P.strong j x k).card*b k) =
      ∑ v ∈ negativeTargets S F P.strong j x, b (failed S F j x v).card := by
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
end ThreeBoundActualTargets

#print axioms ThreeBoundActualTargets.actual_ordinary_prefix_cap
#print axioms ThreeBoundActualTargets.negativeBits_card_le


