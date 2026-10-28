-- Prove2me | Definitions.Def_BS2_b3ba934b_RawConditionalD
-- name    : BS2_b3ba934b_RawConditionalD
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:11:49.03646+00:00
-- url     : https://prove2.me/theorems/74026e70-83c3-49ee-b997-5ad26887d3fd
-- title:
--   Sensitivity separation: RawConditionalD (complete source module)
-- statement:
--   Complete Lean source module `RawConditionalD` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawConditionalD.lean; original SHA-256 a396df94aa1c0ed667ebaacf151ec4de21f141c2f478c8b7b660651645a3ad77; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Complete raw-D expression semantics. Its strict improvement uses the own
strict-component M boundary, while the weak target may remain graded. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalP

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

theorem rawDExpr_bound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k l : Fin n) (P : PairData S F i j) (Q : PairData S F j k) (R : PairData S F k l)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (ho : EntryMatch S F k l R (recipe k) (recipe l))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (caps : Caps) (records : List (List ℕ)) (v : Profile n) (hv : Upper F v)
    (hM : MBound (parent S F) i j k ((rawMExpr n degree (recipe i) (recipe j) (recipe k)).eval v))
    (hP : PBound (parent S F) j k l ((rawPExpr n degree caps records (recipe j) (recipe k) (recipe l)).eval v)) :
    DBound (parent S F) i j k l
      ((rawDExpr n degree caps records (recipe i) (recipe j) (recipe k) (recipe l)).eval v) := by
  classical
  intro x hxj hxk
  have hfirst := (d_of_m_add_p (parent S F) i j k l _ _ hM hP) x hxj hxk
  dsimp only [rawDExpr]
  by_cases hz : (recipe j).tolerance=0 ∧ (recipe l).tolerance=0
  · rw [if_pos hz]
    by_cases hs : (recipe j).same (recipe k)=true
    · rw [if_pos hs]
      have he := matched_same_parent S F j k Q (recipe j) (recipe k) hn hs
      rw [he,hxk] at hxj
      contradiction
    · rw [if_neg hs]
      have hjq : S.tolerance j=0 := hn.weakTolerance.trans hz.1
      have hlq : S.tolerance l=0 := ho.strongTolerance.trans hz.2
      have hkq : S.tolerance k=0 := Nat.eq_zero_of_le_zero (by simpa only [hjq] using Q.tolerances)
      have hkq' : (recipe k).tolerance=0 := hn.strongTolerance.symm.trans hkq
      have hjParent := matched_ordinary_weak S F j k Q (recipe j) (recipe k) hn (ordinary_of_zero _ hz.1)
      have hkParent := matched_ordinary_strong S F j k Q (recipe j) (recipe k) hn (ordinary_of_zero _ hkq')
      have hlParent := matched_ordinary_strong S F k l R (recipe k) (recipe l) ho (ordinary_of_zero _ hz.2)
      rw [hjq] at hjParent
      rw [hkq] at hkParent
      rw [hlq] at hlParent
      rw [hjParent] at hxj
      rw [hkParent] at hxk
      have htij : P.weak 0 ≤ Q.weak 0 := by
        rw [← matched_middle S F recipe i j k P Q hm hn 0]
        exact P.targets 0 (Nat.zero_le _)
      have htjk : Q.weak 0 ≤ Q.strong 0 := Q.targets 0 (Nat.zero_le _)
      have htkl : Q.strong 0 ≤ R.strong 0 := by
        rw [matched_middle S F recipe j k l Q R hn ho 0]
        exact R.targets 0 (Nat.zero_le _)
      have hgil : S.guard i ≤ R.strong 0 :=
        (P.weakGuardTarget 0 (Nat.zero_le _)).trans (htij.trans (htjk.trans htkl))
      have hgli : S.guard l ≤ P.weak 0 :=
        (R.guards.trans (Q.guards.trans P.guards)).trans (P.weakGuardTarget 0 (Nat.zero_le _))
      have hmb := minusExpr_bound_all F hF v hv (P.weak 0) (Q.weak 0) (Q.strong 0) htij
      have hb₀ := bExpr_bound F v hv (P.weak 0) (Q.strong 0) (htij.trans htjk)
      have ha₀ := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
      have hp := plusExpr_bound_all F hF v hv (S.guard k) (S.guard j) (S.guard i) P.guards
      have hb := bExpr_bound F v hv (P.weak 0) (R.strong 0) (htij.trans (htjk.trans htkl))
      have ha := aExpr_bound F v hv (S.guard l) (S.guard i) (R.guards.trans (Q.guards.trans P.guards))
      have hdt := unionExpr_bound_all F hF v hv (P.weak 0) (Q.weak 0) (Q.strong 0) (R.strong 0) htij htkl
      have hdg := unionExpr_bound_all F hF v hv (S.guard l) (S.guard k) (S.guard j) (S.guard i) R.guards P.guards
      have hh := strictD S hT F hF (P.weak 0) (Q.weak 0) (Q.strong 0) (R.strong 0)
        (S.guard i) (S.guard j) (S.guard k) (S.guard l) htij htjk htkl P.guards Q.guards R.guards
        hgil hgli degree _ _ _ _ _ _ _ _ hd hmb hb₀ ha₀ hp hb ha hdt hdg x hxj hxk
      have hsub := ordinary_component_down_subset S F hF (fun _ => P.weak) i
        (P.weak 0) (S.guard i) 0 le_rfl (Nat.zero_le _) (fun d hd => P.weakMono hd) P.weakDef x
      have hc : (flipsTo (parent S F i) false x ∪ flipsTo (parent S F l) true x).card ≤
          (flipsTo (ordinaryParent S F (P.weak 0) (S.guard i) 0) false x ∪
            flipsTo (ordinaryParent S F (R.strong 0) (S.guard l) 0) true x).card := by
        rw [hlParent]
        exact Finset.card_le_card (Finset.union_subset_union hsub (Finset.Subset.refl _))
      rw [eval_min]
      refine le_min (by simpa only [eval_add] using hfirst) ?_
      have hresult := hc.trans hh
      convert hresult using 1
      · congr 1
        ext a
        simp only [Finset.mem_union]
      · simp only [primitiveMExpr,hz.1,ite_true,Nat.sub_zero,
          eval_add,eval_mul,eval_max,eval_zero,apply_ite,eval_maximum_three,max_assoc,Nat.add_assoc,Fin.lt_def,
          hm.weakGuard,hn.weakGuard,hn.strongGuard,ho.strongGuard,
          hm.weakThreshold,hn.weakThreshold,hn.strongThreshold,ho.strongThreshold,threshold_zero]
        split_ifs <;> rfl

  · rw [if_neg hz]
    simpa only [eval_add] using hfirst

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawDExpr_bound


