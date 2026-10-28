-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxPrefixCaps
-- name    : BS2_b3ba934b_MinmaxPrefixCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:39:31.951356+00:00
-- url     : https://prove2.me/theorems/a9bbc02a-e2aa-4b25-8da1-279b63525cd6
-- title:
--   Sensitivity separation: MinmaxPrefixCaps (complete source module)
-- statement:
--   Complete Lean source module `MinmaxPrefixCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxPrefixCaps.lean; original SHA-256 97de12465bd8c49594411eed7c33791760ab60782cb78f2b574c909df9897f5a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Candidate prefix caps for symmetric min/max targets. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRepairCover
import Definitions.Def_BS2_b3ba934b_ActualPrefixCaps
import Definitions.Def_BS2_b3ba934b_ActualQ2Enumeration

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundPrefixCaps
open ThreeBoundActualEnumeration (guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem prefix_partner (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) (w : V)
    (hw : w ∈ targetPrefix S F P.strongLower P.strongUpper j x q)
    (c : Bool) (hc : c ≠ missing S F j x w) :
    F (S.guard j) (child x w c)=true := by
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hw).2
  exact target_partner_guard S F hF i j P x w b ht c hc

theorem prefix_guard_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool)
    (q : ℕ) (v : V) (hv : v ∈ targetPrefix S F t u j x q) :
    (TournamentHighRows.guardFailures S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) v).card ≤ q := by
  rw [guardFailures_eq]
  obtain ⟨b,hb,ht⟩ := (Finset.mem_filter.mp hv).2
  exact ht.2.1.le.trans hb

theorem actual_ordinary_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q a : ℕ)
    (hcap : CandidateCoherence.NoOrdinary S.Adj S.label q a) :
    let T := targetPrefix S F P.strongLower P.strongUpper j x q
    let H := highHeads S F P.strongLower P.strongUpper j x
    T.card ≤ min
      (a-1-((H \ T).filter fun v => (failed S F j x v).card ≤ q).card)
      (a-((H \ T).filter fun v => (failed S F j x v).card ≤ q+1).card) := by
  dsimp only
  have h := ordinary_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x q) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) q a hcap
    (fun w hw c hc => prefix_partner S F hF i j P x q w hw c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strongLower P.strongUpper j x q)
  simpa only [outsideHigh,guardFailures_eq] using h

theorem actual_marked_prefix_cap (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤ ((highHeads S F P.strongLower P.strongUpper j x).filter fun v => (failed S F j x v).card ≤ q+1).card)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m (m*(q+1)) a) :
    let T := targetPrefix S F P.strongLower P.strongUpper j x q
    let H := highHeads S F P.strongLower P.strongUpper j x
    T.card ≤ a-1+(m-((H \ T).filter fun v => (failed S F j x v).card ≤ q+1).card) := by
  dsimp only
  have hm' : m ≤ (eligibleHigh S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F P.strongLower P.strongUpper j x) q).card := by
    simpa only [eligibleHigh,guardFailures_eq] using hm
  have h := marked_prefix_cap S.Adj S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x q) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) q m a hm' hcap
    (fun w hw c hc => prefix_partner S F hF i j P x q w hw c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strongLower P.strongUpper j x q)
  simpa only [outsideHigh,guardFailures_eq] using h


def residualPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (m : ℕ) : ℕ :=
  let H := highHeads S F t u j x
  (((H.toList.map fun w => (failed S F j x w).card-(H.filter (S.Adj w)).card).mergeSort
    (· ≤ ·)).take m).sum

theorem residual_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    ResidualCaps.residual S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F t u j x) w =
      (failed S F j x w).card-((highHeads S F t u j x).filter (S.Adj w)).card := by
  unfold ResidualCaps.residual
  rw [guardFailures_eq]
  rfl

theorem actual_dominator_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (m a : ℕ)
    (hm : m ≤ (highHeads S F P.strongLower P.strongUpper j x).card)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label m a) :
    (targetPrefix S F P.strongLower P.strongUpper j x 0).card ≤
      (targetPrefix S F P.strongLower P.strongUpper j x 0 ∩ highHeads S F P.strongLower P.strongUpper j x).card+(a-1)+
        residualPrefix S F P.strongLower P.strongUpper j x m := by
  have h := dominator_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x 0) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) (highHeads S F P.strongLower P.strongUpper j x).toList
    (Finset.nodup_toList _) (by simp) m a (by simpa using hm) hcap
    (fun w hw c hc => prefix_partner S F hF i j P x 0 w hw c hc)
    (high_guards_true S F hF i j P x)
    (fun v hv => Nat.eq_zero_of_le_zero (prefix_guard_budget S F P.strongLower P.strongUpper j x 0 v hv))
  have he := funext (residual_eq S F P.strongLower P.strongUpper j x)
  simpa only [he,residualPrefix] using h

theorem actual_zero_marked_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤ (highHeads S F P.strongLower P.strongUpper j x).card) (hmq : m ≤ q+2)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m 0 a) :
    (targetPrefix S F P.strongLower P.strongUpper j x q).card ≤
      (targetPrefix S F P.strongLower P.strongUpper j x q ∩ highHeads S F P.strongLower P.strongUpper j x).card+(a-1)+
        residualPrefix S F P.strongLower P.strongUpper j x m := by
  have h := zero_marked_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strongLower P.strongUpper j x q) (highHeads S F P.strongLower P.strongUpper j x)
    (missing S F j x) (highHeads S F P.strongLower P.strongUpper j x).toList
    (Finset.nodup_toList _) (by simp) q m a (by simpa using hm) hmq hcap
    (fun w hw c hc => prefix_partner S F hF i j P x q w hw c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strongLower P.strongUpper j x q)
  have he := funext (residual_eq S F P.strongLower P.strongUpper j x)
  simpa only [he,residualPrefix] using h

end
end ThreeBoundMinmaxCaps

#print axioms ThreeBoundMinmaxCaps.actual_zero_marked_prefix_cap


