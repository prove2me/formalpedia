-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRawM
-- name    : BS2_b3ba934b_MinmaxRawM
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:46:07.621484+00:00
-- url     : https://prove2.me/theorems/a1137c52-cd0c-4d32-aecd-aeecfa138237
-- title:
--   Sensitivity separation: MinmaxRawM (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRawM` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRawM.lean; original SHA-256 3a65d6f3b54da7711dd9f1754657e0becbe8b4cab2cd171378b34e91f8a9714e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact min/max raw-M expression semantics. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRawB

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

theorem rawMOriginalExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    MBound (parent S F) i j k ((rawMOriginalExpr n degree (recipe i) (recipe j) (recipe k)).eval v) := by
  intro x hxj hxk
  have hb := rawBExpr_bound S F hF recipe i j P hm degree hd v hv x hxj
  dsimp only [rawMOriginalExpr]
  by_cases hbad : (Bool.not (recipe j).ordinary = true) ∨ (Bool.not (recipe k).ordinary = true) ∨
      (recipe j).tolerance ≠ (recipe k).tolerance
  · rw [if_pos hbad]
    exact hb
  · rw [if_neg hbad]
    have hjOrd : (recipe j).ordinary=true := by
      cases he : (recipe j).ordinary with
      | false => exact False.elim (hbad (Or.inl (by simp [he])))
      | true => rfl
    have hkOrd : (recipe k).ordinary=true := by
      cases he : (recipe k).ordinary with
      | false => exact False.elim (hbad (Or.inr (Or.inl (by simp [he]))))
      | true => rfl
    have heq : (recipe j).tolerance=(recipe k).tolerance := by
      by_contra he
      exact hbad (Or.inr (Or.inr he))
    have hq : S.tolerance j=S.tolerance k := by rw [hn.weakTolerance,hn.strongTolerance,heq]
    have hjParent := matched_ordinary_weak S F j k Q (recipe j) (recipe k) hn hjOrd
    have hkParent := matched_ordinary_strong S F j k Q (recipe j) (recipe k) hn hkOrd
    rw [hjParent] at hxj
    rw [hkParent,← hq] at hxk
    by_cases hi : (recipe i).ordinary=true
    · rw [if_pos hi]
      have hiParent := matched_ordinary_weak S F i j P (recipe i) (recipe j) hm hi
      have htij : P.weakLower 0 ≤ Q.weakLower 0 := by
        rw [← matched_middle_lower S F recipe i j k P Q hm hn 0 (Nat.zero_le _)]
        exact P.lowerOrder 0 (Nat.zero_le _)
      have hh := ThreeBoundConditionalNumeric.primitiveMExpr_bound S F hF
        (P.weakLower 0) (Q.weakLower 0) (Q.strongLower 0)
        (S.guard i) (S.guard j) (S.guard k) (S.tolerance i) (S.tolerance j)
        (recipe j).base (recipe k).base
        (hn.weakLower 0 (Nat.zero_le _)) (hn.strongLower 0 (Nat.zero_le _))
        hn.weakGuard hn.strongGuard hn.weakTolerance.symm
        htij (Q.lowerOrder 0 (Nat.zero_le _)) P.guards Q.guards P.tolerances degree hd v hv x hxj hxk
      rw [hiParent]
      simpa only [primitiveMExpr,hm.weakLower 0 (Nat.zero_le _),hm.weakGuard,hm.weakTolerance] using hh
    · rw [if_neg hi,eval_min]
      refine le_min hb ?_
      have htop : P.strongUpper (S.tolerance j)=Q.weakLower 0 := by
        apply Fin.ext
        rw [hm.strongUpper _ le_rfl,hn.weakLower 0 (Nat.zero_le _)]
        exact (ordinary_spec (recipe j) hjOrd _ (by rw [← hm.strongTolerance])).2
      have htij : P.weakUpper (S.tolerance j) ≤ Q.weakLower 0 := by
        rw [← htop]
        exact P.upperOrder _ le_rfl
      have hh := ThreeBoundConditionalNumeric.primitiveMExpr_bound S F hF
        (P.weakUpper (S.tolerance j)) (Q.weakLower 0) (Q.strongLower 0)
        (S.guard i) (S.guard j) (S.guard k) (S.tolerance j) (S.tolerance j)
        (recipe j).base (recipe k).base
        (hn.weakLower 0 (Nat.zero_le _)) (hn.strongLower 0 (Nat.zero_le _))
        hn.weakGuard hn.strongGuard hn.weakTolerance.symm
        htij (Q.lowerOrder 0 (Nat.zero_le _)) P.guards Q.guards le_rfl degree hd v hv x hxj hxk
      have hsub := ordinary_upper_component_down_subset S F hF i P.weakLower P.weakUpper
        P.weakLowerMono P.weakUpperMono P.weakLowerUpper P.weakDef (S.tolerance j) P.tolerances x
      have hc := (Finset.card_le_card hsub).trans hh
      rw [hm.weakUpper _ P.tolerances] at hc
      simpa only [primitiveMExpr,hm.weakGuard,hm.strongTolerance] using hc

theorem pairMExpr_row_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hcount : (failed S F j x w).card=d) (hdj : d ≤ S.tolerance j) (hdk : d ≤ S.tolerance k)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (hxk : parent S F k x=false) :
    (flipsTo (parent S F i) false x).card ≤
      (pairMExpr n degree ((recipe i).lowerAt d) ((recipe i).upperAt d) (recipe i).guard d
        ((recipe j).lowerAt d) ((recipe j).upperAt d) (recipe j).guard
        ((recipe k).lowerAt d) ((recipe k).upperAt d) (recipe k).guard).eval v := by
  have hdi : d ≤ S.tolerance i := hdj.trans P.tolerances
  have htjk : P.strongLower d ≤ Q.strongLower d := by
    rw [matched_middle_lower S F recipe i j k P Q hm hn d hdj]
    exact Q.lowerOrder d hdk
  have hujk : P.strongUpper d ≤ Q.strongUpper d := by
    rw [matched_middle_upper S F recipe i j k P Q hm hn d hdj]
    exact Q.upperOrder d hdk
  have ha := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hm0 := minusExpr_bound_all F hF v hv (P.weakLower d) (P.strongLower d) (Q.strongLower d) (P.lowerOrder d hdj)
  have hm1 := minusExpr_bound_all F hF v hv (P.weakUpper d) (P.strongUpper d) (Q.strongUpper d) (P.upperOrder d hdj)
  have hb0 := bExpr_bound F v hv (P.weakLower d) (Q.strongLower d) ((P.lowerOrder d hdj).trans htjk)
  have hb1 := bExpr_bound F v hv (P.weakUpper d) (Q.strongUpper d) ((P.upperOrder d hdj).trans hujk)
  have hp := plusExpr_bound_all F hF v hv (S.guard k) (S.guard j) (S.guard i) P.guards
  have hh := minmax_pairM_parent_row S F hF i j k P Q x w d degree hcount hdj hdk hstrong hxk (hd w)
    _ _ _ _ _ _ ha hm0 hm1 hb0 hb1 hp
  simpa only [pairMExpr,pairMCost,pairMTarget,eval_add,eval_mul,eval_max,eval_zero,eval_ite,Fin.lt_def,
    hm.weakLower d hdi,hm.weakUpper d hdi,hm.strongLower d hdj,hm.strongUpper d hdj,
    hn.strongLower d hdk,hn.strongUpper d hdk,hm.weakGuard,hm.strongGuard,hn.strongGuard] using hh

theorem rawMTierExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hcount : (failed S F j x w).card=d) (hdj : d ≤ S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (hxk : parent S F k x=false) :
    (flipsTo (parent S F i) false x).card ≤ (rawMTierExpr n degree (recipe i) (recipe j) (recipe k) d).eval v := by
  have hdi : d ≤ S.tolerance i := hdj.trans P.tolerances
  have ha := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb0 := bExpr_bound F v hv (P.weakLower d) (P.strongLower d) (P.lowerOrder d hdj)
  have hb1 := bExpr_bound F v hv (P.weakUpper d) (P.strongUpper d) (P.upperOrder d hdj)
  have hh := minmax_oriented_B_row S F hF i j P x w d hcount hdj hstrong _ _ _ ha hb0 hb1
  rw [hd w] at hh
  have hval : (flipsTo (parent S F i) false x).card ≤
      (bExpr n ((recipe i).lowerAt d) ((recipe j).lowerAt d)+
        bExpr n ((recipe i).upperAt d) ((recipe j).upperAt d)+
        (degree-d)*aExpr n (recipe j).guard (recipe i).guard).eval v := by
    simpa only [eval_add,eval_mul,hm.weakLower d hdi,hm.weakUpper d hdi,
      hm.strongLower d hdj,hm.strongUpper d hdj,hm.weakGuard,hm.strongGuard] using hh
  dsimp only [rawMTierExpr]
  by_cases hdk : d ≤ (recipe k).tolerance
  · rw [if_pos hdk,eval_min]
    exact le_min hval (pairMExpr_row_bound S F hF recipe i j k P Q hm hn degree hd v hv x w d hcount hdj
      (by simpa only [hn.strongTolerance] using hdk) hstrong hxk)
  · rw [if_neg hdk]
    exact hval

theorem rawMExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j k : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j) (Q : ThreeBoundMinmaxTransfer.PairData S F j k)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hn : EntryMatch S F j k Q (recipe j) (recipe k))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    MBound (parent S F) i j k ((rawMExpr n degree (recipe i) (recipe j) (recipe k)).eval v) := by
  intro x hxj hxk
  unfold rawMExpr
  by_cases hs : (recipe j).same (recipe k)=true
  · rw [if_pos hs]
    have he := matched_same_parent S F j k Q (recipe j) (recipe k) hn hs
    rw [he,hxk] at hxj
    contradiction
  · rw [if_neg hs,eval_min]
    refine le_min ?_ (rawMOriginalExpr_bound S F hF recipe i j k P Q hm hn degree hd v hv x hxj hxk)
    obtain ⟨w,hcount,hstrong⟩ := (parent_true_iff S F j x).1 hxj
    rw [P.strongDef] at hstrong
    have hh := rawMTierExpr_bound S F hF recipe i j k P Q hm hn degree hd v hv x w
      (failed S F j x w).card rfl hcount hstrong hxk
    apply hh.trans
    simp only [Expr.eval_maximum,List.map_map]
    apply le_maximum_of_mem
    apply List.mem_map.mpr
    exact ⟨(failed S F j x w).card,List.mem_range.mpr (by rw [← hm.strongTolerance]; omega),rfl⟩

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawMExpr_bound


