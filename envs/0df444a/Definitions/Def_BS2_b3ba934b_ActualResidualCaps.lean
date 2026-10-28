-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualResidualCaps
-- name    : BS2_b3ba934b_ActualResidualCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:31:48.495585+00:00
-- url     : https://prove2.me/theorems/3eb1b19d-d52e-4bf8-a5da-26a378d8c571
-- title:
--   Sensitivity separation: ActualResidualCaps (complete source module)
-- statement:
--   Complete Lean source module `ActualResidualCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualResidualCaps.lean; original SHA-256 51b59f64dad351405b415f3034ed5f5d52a9cd317d6020adfa4c1fc557a46782; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Residual marker bounds in the coordinates of the actual Boolean stage. -/
import Definitions.Def_BS2_b3ba934b_ActualTargetAccounting

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundActualResidualCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundActualEnumeration
open ThreeBoundActualTargets ThreeBoundPrefixCaps
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def residualPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (m : ℕ) : ℕ :=
  let H := highHeads S F t j x
  (((H.toList.map fun w => (failed S F j x w).card-(H.filter (S.Adj w)).card).mergeSort
    (· ≤ ·)).take m).sum

theorem residual_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (w : V) :
    ResidualCaps.residual S.Adj S.label (fun z => F (S.guard j) z = true)
      (child x) (highHeads S F t j x) w =
      (failed S F j x w).card-((highHeads S F t j x).filter (S.Adj w)).card := by
  unfold ResidualCaps.residual
  rw [guardFailures_eq]
  rfl

theorem actual_dominator_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (m a : ℕ)
    (hm : m ≤ (highHeads S F P.strong j x).card)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label m a) :
    (targetPrefix S F P.strong j x 0).card ≤
      (targetPrefix S F P.strong j x 0 ∩ highHeads S F P.strong j x).card+(a-1)+
        residualPrefix S F P.strong j x m := by
  have h := dominator_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strong j x 0) (highHeads S F P.strong j x)
    (missing S F P.strong j x) (highHeads S F P.strong j x).toList
    (Finset.nodup_toList _) (by simp) m a (by simpa using hm) hcap
    (fun w hw c hc => nonmissing_partner S F hF i j P x w (Finset.mem_filter.mp hw).2.1 c hc)
    (high_guards_true S F hF i j P x)
    (fun v hv => Nat.eq_zero_of_le_zero (prefix_guard_budget S F P.strong j x 0 v hv))
  have he := funext (residual_eq S F P.strong j x)
  simpa only [he,residualPrefix] using h

theorem actual_zero_marked_prefix_cap (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q m a : ℕ)
    (hm : m ≤ (highHeads S F P.strong j x).card) (hmq : m ≤ q+2)
    (hcap : ResidualCaps.MarkedCardBound S.Adj S.label q m 0 a) :
    (targetPrefix S F P.strong j x q).card ≤
      (targetPrefix S F P.strong j x q ∩ highHeads S F P.strong j x).card+(a-1)+
        residualPrefix S F P.strong j x m := by
  have h := zero_marked_prefix_cap S.Adj hR S.label (fun z => F (S.guard j) z = true)
    (child x) (targetPrefix S F P.strong j x q) (highHeads S F P.strong j x)
    (missing S F P.strong j x) (highHeads S F P.strong j x).toList
    (Finset.nodup_toList _) (by simp) q m a (by simpa using hm) hmq hcap
    (fun w hw c hc => nonmissing_partner S F hF i j P x w (Finset.mem_filter.mp hw).2.1 c hc)
    (high_guards_true S F hF i j P x)
    (prefix_guard_budget S F P.strong j x q)
  have he := funext (residual_eq S F P.strong j x)
  simpa only [he,residualPrefix] using h

end
end ThreeBoundActualResidualCaps

#print axioms ThreeBoundActualResidualCaps.actual_zero_marked_prefix_cap


