-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRawD
-- name    : BS2_b3ba934b_MinmaxRawD
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:48:19.429298+00:00
-- url     : https://prove2.me/theorems/c71d449f-01bd-40c2-af5b-7a2386870f48
-- title:
--   Sensitivity separation: MinmaxRawD (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRawD` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRawD.lean; original SHA-256 cf914691df66d1d970220cea6dd0e30522c39821d87b78a5e6904ce893a91443; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact oriented strict-D numerical semantics for min/max parents. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRawP

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawDExpr_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k l : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (Q : ThreeBoundMinmaxTransfer.PairData S F j k) (R : ThreeBoundMinmaxTransfer.PairData S F k l)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (ho : EntryMatch S F k l R (recipe k) (recipe l))
    (degree pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v)
    (hM : MBound (parent S F) i j k ((rawMExpr n degree (recipe i) (recipe j) (recipe k)).eval v))
    (hP : PBound (parent S F) j k l ((rawPExpr n pcross rawA (recipe j) (recipe k) (recipe l)).eval v)) :
    DBound (parent S F) i j k l
      ((rawDExpr n degree pcross rawA (recipe i) (recipe j) (recipe k) (recipe l)).eval v) := by
  classical
  intro x hxj hxk
  have hfirst : (@Union.union (Finset ((V × Bool) × I))
      (@Finset.instUnion ((V × Bool) × I) (fun a b => Classical.propDecidable (a=b)))
      (flipsTo (parent S F i) false x) (flipsTo (parent S F l) true x)).card ≤
      (rawMExpr n degree (recipe i) (recipe j) (recipe k)+rawPExpr n pcross rawA (recipe j) (recipe k) (recipe l)).eval v :=
    (@Finset.card_union_le ((V × Bool) × I) (fun a b => Classical.propDecidable (a=b)) _ _).trans
      (Nat.add_le_add (hM x hxj hxk) (hP x hxj hxk))
  dsimp only [rawDExpr]
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k Q (recipe j) (recipe k) hn hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs]
    by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0 ∧
        (recipe l).plain=true ∧ (recipe k).upperAt 0 ≤ (recipe l).lowerAt 0
    · rw [if_pos hz,eval_min]
      refine le_min ?_ ?_
      · exact hfirst
      · have hjq : S.tolerance j=0 := hm.strongTolerance.trans hz.1
        have hlq : S.tolerance l=0 := ho.strongTolerance.trans hz.2.1
        have hlplain : R.strongUpper 0=R.strongLower 0 := by
          apply Fin.ext
          rw [ho.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _)]
          exact (plain_spec (recipe l) hz.2.2.1 0 (Nat.zero_le _)).symm
        have hldef : ∀ u z, S.target l 0 u z=mm F (R.strongLower 0) (R.strongLower 0) u z := by
          intro u z
          rw [R.strongDef,hlplain]
        have htjk : P.strongLower 0 ≤ Q.strongLower 0 := by
          rw [matched_middle_lower S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
          exact Q.lowerOrder 0 (Nat.zero_le _)
        have hujk : P.strongUpper 0 ≤ Q.strongUpper 0 := by
          rw [matched_middle_upper S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
          exact Q.upperOrder 0 (Nat.zero_le _)
        have hukl : Q.strongUpper 0 ≤ R.strongLower 0 := by
          change (Q.strongUpper 0).val ≤ (R.strongLower 0).val
          rw [hn.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _)]
          exact hz.2.2.2
        have htkl := (Q.strongLowerUpper 0 (Nat.zero_le _)).trans hukl
        have htij := P.lowerOrder 0 (Nat.zero_le _)
        have huij := P.upperOrder 0 (Nat.zero_le _)
        have haM := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
        have hm0 := minusExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) htij
        have hm1 := minusExpr_bound_all F hF v hv (P.weakUpper 0) (P.strongUpper 0) (Q.strongUpper 0) huij
        have hbm0 := bExpr_bound F v hv (P.weakLower 0) (Q.strongLower 0) (htij.trans htjk)
        have hbm1 := bExpr_bound F v hv (P.weakUpper 0) (Q.strongUpper 0) (huij.trans hujk)
        have hp := plusExpr_bound_all F hF v hv (S.guard k) (S.guard j) (S.guard i) P.guards
        have hb0 := bExpr_bound F v hv (P.weakLower 0) (R.strongLower 0) (htij.trans (htjk.trans htkl))
        have hb1 := bExpr_bound F v hv (P.weakUpper 0) (R.strongLower 0) (huij.trans (hujk.trans hukl))
        have haD := aExpr_bound F v hv (S.guard l) (S.guard i) (R.guards.trans (Q.guards.trans P.guards))
        have hdt := unionExpr_bound_all F hF v hv (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) (R.strongLower 0) htij htkl
        have hdg := unionExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) (S.guard i) R.guards P.guards
        have hh := minmax_strictD_parent S hT F hF i j k l P Q hjq hlq (R.strongLower 0) hldef
          (hujk.trans hukl) hukl R.guards degree _ _ _ _ _ _ _ _ _ _ _ hd
          haM hm0 hm1 hbm0 hbm1 hp hb0 hb1 haD hdt hdg x hxj hxk
        simpa only [pairMExpr,pairMCost,pairMTarget,eval_add,eval_mul,eval_max,eval_zero,eval_ite,Fin.lt_def,
          hm.weakLower 0 (Nat.zero_le _),hm.weakUpper 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _),
          hn.strongLower 0 (Nat.zero_le _),hn.strongUpper 0 (Nat.zero_le _),ho.strongLower 0 (Nat.zero_le _),
          hm.weakGuard,hm.strongGuard,hn.strongGuard,ho.strongGuard] using hh
    · rw [if_neg hz]
      exact hfirst

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawDExpr_bound


