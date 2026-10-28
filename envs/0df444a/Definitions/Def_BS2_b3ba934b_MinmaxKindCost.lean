-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxKindCost
-- name    : BS2_b3ba934b_MinmaxKindCost
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:52:26.899345+00:00
-- url     : https://prove2.me/theorems/7de8df29-bd69-4bb8-8d34-0f619988d712
-- title:
--   Sensitivity separation: MinmaxKindCost (complete source module)
-- statement:
--   Complete Lean source module `MinmaxKindCost` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxKindCost.lean; original SHA-256 1f0b753a97816ed9c992c7fd27b4fb72f96a02dc7dc7fd4aa4108b775d55a087; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Every actual min/max high-head type satisfies its numerical head cost. -/
import Definitions.Def_BS2_b3ba934b_MinmaxHeadExpr
import Definitions.Def_BS2_b3ba934b_MinmaxKindFacts

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundMinmaxQ2
open ThreeBoundHeadCharge (headBits guardParts)
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem guardCost_eval_guard (a c : ThreeBoundMinmaxNumeric.Entry) (v : Profile n)
    (k h : ℕ) (hk : ¬ k ≤ 2) :
    (guardCost n a c k h).eval v =
      ThreeBoundHeadCharge.guardCost ((bExpr n c.guard (c.lowerAt (guardLevel k))).eval v)
        ((bExpr n c.guard (c.lowerAt (guardLevel k))).eval v+
          (bExpr n c.guard (c.upperAt (guardLevel k))).eval v) h := by
  unfold guardCost
  rw [if_neg hk]
  simp only [guardLevel,ThreeBoundMinmaxNumeric.eval_ite,eval_add,eval_zero,ThreeBoundHeadCharge.guardCost]

theorem headCost_zero_le (a c : ThreeBoundMinmaxNumeric.Entry) (v : Profile n) (k h : ℕ) :
    (headCost n a c k 0).eval v ≤ (headCost n a c k h).eval v := by
  have he : (guardCost n a c k 0).eval v=0 := by
    by_cases hk : k ≤ 2 <;> simp [guardCost,hk,Expr.eval]
  simp only [headCost,eval_add,he,Nat.add_zero]
  omega

theorem actual_kind_headCost_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false)
    (hQ : S.tolerance j ≤ 2) (w : V) (k : Fin 8)
    (hk : ThreeBoundHighTypes.OfKind 2
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) k) :
    (headBits w (actualHeadParts S F P.strongLower P.strongUpper j x w)).card ≤
      (headCost n a c k.val (min 2 (ThreeBoundAccounting.incoming S.Adj
        (guardSources S F P.strongLower P.strongUpper j x) w))).eval v := by
  have hw : w ∈ highHeads S F P.strongLower P.strongUpper j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ThreeBoundHighTypes.ofKind_high 2 _ _ k hk⟩
  have ht : (headBits w (targetParts S F P.strongLower P.strongUpper j x w)).card ≤
      (targetCost n a c k.val).eval v := by
    by_cases hlow : k.val ≤ 2
    · have hp := kind_positive 2 _ _ k hk hlow
      simpa only [targetCost,if_pos hlow] using targetParts_positive_bound S F hF i j P a c hm v hv x hoff w k.val hp
    · by_cases hhigh : 6 ≤ k.val
      · have hp := kind_overlap _ _ k hk hhigh
        simpa only [targetCost,if_neg hlow,if_pos hhigh] using
          targetParts_positive_bound S F hF i j P a c hm v hv x hoff w (k.val-5) hp
      · have hn := kind_no_positive S F P.strongLower P.strongUpper j x w hQ k hk (by omega) (by omega)
        rw [targetParts_zero S F hF i j P x w hw hn]
        exact Nat.zero_le _
  have hg : (headBits w (guardParts F (S.guard j) (child x w)
      (hitChildren S F P.strongLower P.strongUpper j x w))).card ≤
      (guardCost n a c k.val (min 2 (ThreeBoundAccounting.incoming S.Adj
        (guardSources S F P.strongLower P.strongUpper j x) w))).eval v := by
    by_cases hlow : k.val ≤ 2
    · simpa only [guardCost,if_pos hlow,eval_mul] using
        guardParts_weak_bound S F hF i j P a c hm v hv x hoff w hw
    · rw [guardCost_eval_guard a c v _ _ hlow]
      exact guardParts_candidate_bound S F i j P a c hm v hv x w (guardLevel k.val)
        (kind_guard _ _ k hk (by omega))
  exact (head_card_le S F P.strongLower P.strongUpper j x w).trans (Nat.add_le_add ht hg)

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.actual_kind_headCost_bound


