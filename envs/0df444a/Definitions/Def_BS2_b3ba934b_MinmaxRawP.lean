-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRawP
-- name    : BS2_b3ba934b_MinmaxRawP
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:47:07.852061+00:00
-- url     : https://prove2.me/theorems/8a7c1d7f-3b6d-441d-a3e4-53af517bb298
-- title:
--   Sensitivity separation: MinmaxRawP (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRawP` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRawP.lean; original SHA-256 c67c1d4ccfc49e28614d6458a18388a4e9d5ba65362bd79e66bdcd147ee7f830; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The ordinary strict-positive refinements applied to actual min/max parents. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRawM

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawPExpr_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (j k l : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F j k) (Q : ThreeBoundMinmaxTransfer.PairData S F k l)
    (hm : EntryMatch S F j k P (recipe j) (recipe k))
    (hn : EntryMatch S F k l Q (recipe k) (recipe l))
    (pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (pcross+1))
    (v : Profile n) (hv : Upper F v)
    (hA : ABound (parent S F) k l ((rawA (recipe k) (recipe l)).eval v)) :
    PBound (parent S F) j k l ((rawPExpr n pcross rawA (recipe j) (recipe k) (recipe l)).eval v) := by
  intro x hxj hxk
  have hfirst := hA x hxk
  dsimp only [rawPExpr]
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k P (recipe j) (recipe k) hm hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs]
    by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0 ∧
        (recipe j).plain=true ∧ (recipe k).plain=true ∧ (recipe l).plain=true
    · rw [if_pos hz]
      have hjq : S.tolerance j=0 := hm.weakTolerance.trans hz.1
      have hlq : S.tolerance l=0 := hn.strongTolerance.trans hz.2.1
      have hkq : S.tolerance k=0 := Nat.eq_zero_of_le_zero (by simpa only [hjq] using P.tolerances)
      have hkq' : (recipe k).tolerance=0 := hm.strongTolerance.symm.trans hkq
      have hjParent := matched_ordinary_weak S F j k P (recipe j) (recipe k) hm
        (ordinary_of_zero_plain _ hz.1 hz.2.2.1)
      have hkParent := matched_ordinary_strong S F j k P (recipe j) (recipe k) hm
        (ordinary_of_zero_plain _ hkq' hz.2.2.2.1)
      have hlParent := matched_ordinary_strong S F k l Q (recipe k) (recipe l) hn
        (ordinary_of_zero_plain _ hz.2.1 hz.2.2.2.2)
      rw [hjq] at hjParent
      rw [hkq] at hkParent
      rw [hlq] at hlParent
      rw [hjParent] at hxj
      rw [hkParent] at hxk
      have htjk : P.weakLower 0 ≤ P.strongLower 0 := P.lowerOrder 0 (Nat.zero_le _)
      have htkl : P.strongLower 0 ≤ Q.strongLower 0 := by
        rw [matched_middle_lower S F recipe j k l P Q hm hn 0 (Nat.zero_le _)]
        exact Q.lowerOrder 0 (Nat.zero_le _)
      have hgjtl : S.guard j ≤ Q.strongLower 0 :=
        (P.weakGuardTarget 0 (Nat.zero_le _)).trans (htjk.trans htkl)
      have hgltj : S.guard l ≤ P.weakLower 0 :=
        (Q.guards.trans P.guards).trans (P.weakGuardTarget 0 (Nat.zero_le _))
      have hgltl : S.guard l ≤ Q.strongLower 0 := Q.guardTarget 0 (Nat.zero_le _)
      have ha := aExpr_bound F v hv (S.guard j) (Q.strongLower 0) hgjtl
      have hb := bExpr_bound F v hv (S.guard l) (P.weakLower 0) hgltj
      have hp := plusExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) htkl
      have hmg := minusExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) Q.guards
      have hbk := bExpr_bound F v hv (S.guard l) (P.strongLower 0) (hgltj.trans htjk)
      have hbl := bExpr_bound F v hv (S.guard l) (Q.strongLower 0) hgltl
      have hmt := minusExpr_bound_all F hF v hv (S.guard l) (P.weakLower 0) (P.strongLower 0) hgltj
      have hu := unionExpr_bound_all F hF v hv (S.guard l) (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) hgltj htkl
      have hbasic := strictP_basic S hT F hF (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0)
        (S.guard j) (S.guard k) (S.guard l) htkl Q.guards hgjtl hgltj hgltl
        pcross _ _ _ _ hcap hb ha hp hmg x hxj hxk
      have hrefined := strictP_refined S hT F hF (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0)
        (S.guard j) (S.guard k) (S.guard l) htjk htkl P.guards Q.guards hgjtl hgltj hgltl
        pcross _ _ _ _ _ _ hcap ha hmt hbk hbl hu hmg x hxj hxk
      rw [eval_min,eval_min]
      refine le_min (le_min hfirst ?_) ?_
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hn.strongLower 0 (Nat.zero_le _)] using hbasic
      · rw [hlParent]
        simpa only [eval_add,eval_mul,eval_max,eval_zero,eval_ite,Fin.lt_def,
          hm.weakGuard,hm.strongGuard,hn.strongGuard,
          hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hn.strongLower 0 (Nat.zero_le _)] using hrefined
    · rw [if_neg hz]
      exact hfirst

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawPExpr_bound


