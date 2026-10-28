-- Prove2me | Definitions.Def_BS2_b3ba934b_RawConditionalP
-- name    : BS2_b3ba934b_RawConditionalP
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:08:16.788257+00:00
-- url     : https://prove2.me/theorems/11687ca0-2606-4fbe-8c9c-bf07387db923
-- title:
--   Sensitivity separation: RawConditionalP (complete source module)
-- statement:
--   Complete Lean source module `RawConditionalP` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawConditionalP.lean; original SHA-256 fc07b26e701495a0f168a0ab9aa98fd76ad8d24ab90179fdbd2d0f72c4e27d3f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Complete raw-P expression semantics: the ordinary A fallback and both
strict conditional improvements apply to the actual Bool parent. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalM

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawPExpr_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (j k l : Fin n) (P : PairData S F j k) (Q : PairData S F k l)
    (hm : EntryMatch S F j k P (recipe j) (recipe k))
    (hn : EntryMatch S F k l Q (recipe k) (recipe l))
    (degree : ℕ) (caps : Caps) (records : List (List ℕ))
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (caps.pcross+1))
    (v : Profile n) (hv : Upper F v)
    (hA : ABound (parent S F) k l ((rawAExpr n caps records (recipe k) (recipe l)).eval v)) :
    PBound (parent S F) j k l ((rawPExpr n degree caps records (recipe j) (recipe k) (recipe l)).eval v) := by
  classical
  intro x hxj hxk
  have hfirst := hA x hxk
  dsimp only [rawPExpr]
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k P (recipe j) (recipe k) hm hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs]
    by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0
    · rw [if_pos hz]
      have hjq : S.tolerance j=0 := hm.weakTolerance.trans hz.1
      have hlq : S.tolerance l=0 := hn.strongTolerance.trans hz.2
      have hkq : S.tolerance k=0 := Nat.eq_zero_of_le_zero (by simpa only [hjq] using P.tolerances)
      have hkq' : (recipe k).tolerance=0 := hm.strongTolerance.symm.trans hkq
      have hjParent := matched_ordinary_weak S F j k P (recipe j) (recipe k) hm (ordinary_of_zero _ hz.1)
      have hkParent := matched_ordinary_strong S F j k P (recipe j) (recipe k) hm (ordinary_of_zero _ hkq')
      have hlParent := matched_ordinary_strong S F k l Q (recipe k) (recipe l) hn (ordinary_of_zero _ hz.2)
      rw [hjq] at hjParent
      rw [hkq] at hkParent
      rw [hlq] at hlParent
      rw [hjParent] at hxj
      rw [hkParent] at hxk
      have htjk : P.weak 0 ≤ P.strong 0 := P.targets 0 (Nat.zero_le _)
      have htkl : P.strong 0 ≤ Q.strong 0 := by
        rw [matched_middle S F recipe j k l P Q hm hn 0]
        exact Q.targets 0 (Nat.zero_le _)
      have hgjtl : S.guard j ≤ Q.strong 0 :=
        (P.weakGuardTarget 0 (Nat.zero_le _)).trans (htjk.trans htkl)
      have hgltj : S.guard l ≤ P.weak 0 :=
        (Q.guards.trans P.guards).trans (P.weakGuardTarget 0 (Nat.zero_le _))
      have hgltl : S.guard l ≤ Q.strong 0 := Q.guardTarget 0 (Nat.zero_le _)
      have ha := aExpr_bound F v hv (S.guard j) (Q.strong 0) hgjtl
      have hb := bExpr_bound F v hv (S.guard l) (P.weak 0) hgltj
      have hp := plusExpr_bound_all F hF v hv (P.weak 0) (P.strong 0) (Q.strong 0) htkl
      have hmg := minusExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) Q.guards
      have hbₖ := bExpr_bound F v hv (S.guard l) (P.strong 0) (hgltj.trans htjk)
      have hbₗ := bExpr_bound F v hv (S.guard l) (Q.strong 0) hgltl
      have hmt := minusExpr_bound_all F hF v hv (S.guard l) (P.weak 0) (P.strong 0) hgltj
      have hu := unionExpr_bound_all F hF v hv (S.guard l) (P.weak 0) (P.strong 0) (Q.strong 0) hgltj htkl
      have hbasic := strictP_basic S hT F hF (P.weak 0) (P.strong 0) (Q.strong 0)
        (S.guard j) (S.guard k) (S.guard l) htkl Q.guards hgjtl hgltj hgltl
        caps.pcross _ _ _ _ hcap hb ha hp hmg x hxj hxk
      have hrefined := strictP_refined S hT F hF (P.weak 0) (P.strong 0) (Q.strong 0)
        (S.guard j) (S.guard k) (S.guard l) htjk htkl P.guards Q.guards hgjtl hgltj hgltl
        caps.pcross _ _ _ _ _ _ hcap ha hmt hbₖ hbₗ hu hmg x hxj hxk
      rw [eval_min,eval_min]
      refine le_min (le_min hfirst ?_) ?_
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakThreshold,hm.strongThreshold,hn.strongThreshold,threshold_zero] using hbasic
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,eval_zero,apply_ite,eval_maximum_three,max_assoc,Fin.lt_def,
          hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakThreshold,hm.strongThreshold,hn.strongThreshold,threshold_zero] using hrefined
    · rw [if_neg hz]
      exact hfirst

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawPExpr_bound


