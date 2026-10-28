-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRawB
-- name    : BS2_b3ba934b_MinmaxRawB
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:42:13.822552+00:00
-- url     : https://prove2.me/theorems/c8ca47f2-ac36-475b-8deb-b398b2a0e6b4
-- title:
--   Sensitivity separation: MinmaxRawB (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRawB` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRawB.lean; original SHA-256 d8370c9499a8edd3db0c96451bdf99426d33a3f6dccc680e3b7ac7dec293e5c0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual Boolean semantics of the numeric min/max raw-B expression. -/
import Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch

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

theorem rawBExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    BBound (parent S F) i j ((rawBExpr n degree (recipe i) (recipe j)).eval v) := by
  intro x hx
  obtain ⟨w,hcount,hwin⟩ := (parent_true_iff S F j x).1 hx
  let d := (failed S F j x w).card
  have hdq : d ≤ S.tolerance j := hcount
  have hdi : d ≤ S.tolerance i := hdq.trans P.tolerances
  have hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true := by
    simpa only [P.strongDef] using hwin
  have ha := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb0 := bExpr_bound F v hv (P.weakLower d) (P.strongLower d) (P.lowerOrder d hdq)
  have hb1 := bExpr_bound F v hv (P.weakLower d) (P.strongUpper d)
    ((P.lowerOrder d hdq).trans (P.strongLowerUpper d hdq))
  have hbu := bExpr_bound F v hv (P.weakUpper d) (P.strongUpper d) (P.upperOrder d hdq)
  have hm0 := minusExpr_bound_all F hF v hv (P.weakLower d) (P.strongLower d) (P.weakUpper d) (P.lowerOrder d hdq)
  have hh := minmax_B_row S F hF i j P x w d rfl hdq hstrong _ _ _ _ _ ha hb0 hb1 hbu hm0
  rw [hd w] at hh
  have hgate : ((recipe i).tolerance ≤ d ∨ (recipe j).lowerAt d<(recipe i).lowerAt (d+1) ∨
      (recipe j).upperAt d<(recipe i).upperAt (d+1)) ↔
      ¬(d+1 ≤ S.tolerance i ∧ P.weakLower (d+1) ≤ P.strongLower d ∧ P.weakUpper (d+1) ≤ P.strongUpper d) := by
    rw [← hm.weakTolerance]
    by_cases hnext : d+1 ≤ S.tolerance i
    · rw [← hm.weakLower (d+1) hnext,← hm.weakUpper (d+1) hnext,
        ← hm.strongLower d hdq,← hm.strongUpper d hdq]
      change (_ ∨ (P.strongLower d).val<(P.weakLower (d+1)).val ∨
        (P.strongUpper d).val<(P.weakUpper (d+1)).val) ↔
        ¬(_ ∧ (P.weakLower (d+1)).val ≤ (P.strongLower d).val ∧
          (P.weakUpper (d+1)).val ≤ (P.strongUpper d).val)
      omega
    · have hle : S.tolerance i ≤ d := by omega
      simp only [hle,true_or,hnext,false_and,not_false_eq_true]
  have hrow : (flipsTo (parent S F i) false x).card ≤
      (max (bExpr n ((recipe i).lowerAt d) ((recipe j).lowerAt d)+
        bExpr n ((recipe i).lowerAt d) ((recipe j).upperAt d))
        (if (recipe j).lowerAt d<(recipe i).upperAt d then
          bExpr n ((recipe i).upperAt d) ((recipe j).upperAt d)+
          minusExpr n ((recipe i).lowerAt d) ((recipe j).lowerAt d) ((recipe i).upperAt d) else 0)+
        if (recipe i).tolerance ≤ d ∨ (recipe j).lowerAt d<(recipe i).lowerAt (d+1) ∨
          (recipe j).upperAt d<(recipe i).upperAt (d+1)
        then (degree-d)*aExpr n (recipe j).guard (recipe i).guard else 0).eval v := by
    by_cases hs : d+1 ≤ S.tolerance i ∧ P.weakLower (d+1) ≤ P.strongLower d ∧ P.weakUpper (d+1) ≤ P.strongUpper d
    · rw [if_neg (fun h => (hgate.mp h) hs)]
      simpa only [if_pos hs,eval_add,eval_max,eval_mul,eval_zero,eval_ite,Fin.lt_def,
        hm.weakLower d hdi,hm.weakUpper d hdi,hm.strongLower d hdq,hm.strongUpper d hdq,
        hm.weakGuard,hm.strongGuard] using hh
    · rw [if_pos (hgate.mpr hs)]
      simpa only [if_neg hs,eval_add,eval_max,eval_mul,eval_zero,eval_ite,Fin.lt_def,
        hm.weakLower d hdi,hm.weakUpper d hdi,hm.strongLower d hdq,hm.strongUpper d hdq,
        hm.weakGuard,hm.strongGuard] using hh
  apply hrow.trans
  simp only [rawBExpr,Expr.eval_maximum,List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  exact ⟨d,List.mem_range.mpr (by rw [← hm.strongTolerance]; omega),rfl⟩

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawBExpr_bound


