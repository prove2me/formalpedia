-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxHeadExpr
-- name    : BS2_b3ba934b_MinmaxHeadExpr
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:47:30.42106+00:00
-- url     : https://prove2.me/theorems/dd0b2386-545e-4334-872d-2b393a101e17
-- title:
--   Sensitivity separation: MinmaxHeadExpr (complete source module)
-- statement:
--   Complete Lean source module `MinmaxHeadExpr` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxHeadExpr.lean; original SHA-256 0ef1949a2c69f276d108a7869163eb1cc534cf0272864c0de103bf9ad13b4b34; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The shared histogram head costs bound actual min/max sensitivity sets. -/
import Definitions.Def_BS2_b3ba934b_MinmaxNegativeExpr
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover ThreeBoundMinmaxHeads
open ThreeBoundHeadCharge (headBits headBits_card guardParts card_bool_finset)
open ThreeBoundHeadExpressions (plusExpr_bound_all)
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem targetParts_positive_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false) (w : V) (b : ℕ)
    (hb : PositiveCandidate S F P.strongLower P.strongUpper j x w b) :
    (headBits w (targetParts S F P.strongLower P.strongUpper j x w)).card ≤
      (positiveExpr n a c b).eval v := by
  have ht : targetAt S F P.strongLower P.strongUpper j x w := ⟨b,hb.1⟩
  have he : targetParts S F P.strongLower P.strongUpper j x w =
      upPart F (P.strongLower b) (P.strongUpper b) (child x w) := by
    funext d
    simp only [targetParts,if_pos ht,hb.1.2.1]
  rw [he,headBits_card]
  have hbi := hb.1.1.trans P.tolerances
  have htord := P.lowerOrder b hb.1.1
  have huord := P.upperOrder b hb.1.1
  have h := minmax_positive_cost F hF (S.guard j) (P.weakLower b) (P.weakUpper b)
    (P.strongLower b) (P.strongUpper b) htord huord (child x w) hb.2
    (weak_target_false S F hF i j P x hoff w b hb.1.1 hb.1.2.1.le)
    _ _ _ (plusExpr_bound_all F hF v hv _ _ _ htord)
    (plusExpr_bound_all F hF v hv _ _ _ huord)
    (plusExpr_bound_all F hF v hv _ _ _ huord)
  simpa only [positiveExpr,eval_max,eval_mul,hm.strongGuard,
    hm.weakLower b hbi,hm.weakUpper b hbi,
    hm.strongLower b hb.1.1,hm.strongUpper b hb.1.1] using h

theorem targetParts_zero (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool) (w : V)
    (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x)
    (hn : ¬ ∃ b, PositiveCandidate S F P.strongLower P.strongUpper j x w b) :
    (headBits w (targetParts S F P.strongLower P.strongUpper j x w)).card=0 := by
  have ht : ¬ targetAt S F P.strongLower P.strongUpper j x w := by
    rintro ⟨b,hb⟩
    exact hn ⟨b,hb,high_guards_true S F hF i j P x w hw⟩
  simp [headBits_card,targetParts,ht]

theorem guardParts_weak_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false) (w : V)
    (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x) :
    (headBits w (guardParts F (S.guard j) (child x w)
      (hitChildren S F P.strongLower P.strongUpper j x w))).card ≤
      min 2 (ThreeBoundAccounting.incoming S.Adj (guardSources S F P.strongLower P.strongUpper j x) w)*
        (bExpr n c.guard a.guard).eval v := by
  let hit := hitChildren S F P.strongLower P.strongUpper j x w
  let s := (bExpr n c.guard a.guard).eval v
  have hb : BBound F (S.guard j) (S.guard i) s := by
    have h := bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
    simpa only [hm.strongGuard,hm.weakGuard] using h
  have hbound : ∀ d ∈ hit, (flipsTo (F (S.guard j)) false (child x w d)).card ≤ s := by
    intro d hd
    obtain ⟨u,hu,hR,hl⟩ := (ThreeBoundAccounting.mem_hits _ _ _ w d).1 hd
    obtain ⟨b,hb'⟩ := (Finset.mem_filter.mp hu).2
    have hwf : w ∈ failed S F j x u := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hR,high_guards_true S F hF i j P x w hw _⟩
    have he := guard_hit_eligible S F hF i j P x hoff u b hb' w hwf
    rw [hl] at he
    exact hb _ he
  have hfirst : (headBits w (guardParts F (S.guard j) (child x w) hit)).card ≤ hit.card*s := by
    rw [headBits_card,card_bool_finset]
    by_cases h0 : false ∈ hit <;> by_cases h1 : true ∈ hit
    · have b0 := hbound false h0
      have b1 := hbound true h1
      simp only [guardParts,if_pos h0,if_pos h1]
      omega
    · have b0 := hbound false h0
      simp only [guardParts,if_pos h0,if_neg h1,Finset.card_empty]
      omega
    · have b1 := hbound true h1
      simp only [guardParts,if_neg h0,if_pos h1,Finset.card_empty]
      omega
    · simp [guardParts,h0,h1]
  exact hfirst.trans (Nat.mul_le_mul_right s
    (ThreeBoundAccounting.hits_card_le_capped S.Adj S.label _ w))

theorem guardParts_candidate_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ)
    (hb : GuardCandidate S F P.strongLower P.strongUpper j x w b) :
    (headBits w (guardParts F (S.guard j) (child x w)
      (hitChildren S F P.strongLower P.strongUpper j x w))).card ≤
      ThreeBoundHeadCharge.guardCost
        ((bExpr n c.guard (c.lowerAt b)).eval v)
        ((bExpr n c.guard (c.lowerAt b)).eval v+(bExpr n c.guard (c.upperAt b)).eval v)
        (min 2 (ThreeBoundAccounting.incoming S.Adj
          (guardSources S F P.strongLower P.strongUpper j x) w)) := by
  have hlo := bExpr_bound F v hv (S.guard j) (P.strongLower b) (P.guardTarget b hb.1)
  have hhi := bExpr_bound F v hv (S.guard j) (P.strongUpper b)
    ((P.guardTarget b hb.1).trans (P.strongLowerUpper b hb.1))
  have h := minmax_guard_cost F (S.guard j) (P.strongLower b) (P.strongUpper b)
    (child x w) (hitChildren S F P.strongLower P.strongUpper j x w) w hb.2.2 _ _ _ hlo hhi
    (ThreeBoundAccounting.hits_card_le_capped S.Adj S.label _ w)
  simpa only [hm.strongGuard,hm.strongLower b hb.1,hm.strongUpper b hb.1] using h

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.targetParts_positive_bound
#print axioms ThreeBoundMinmaxA.guardParts_candidate_bound


