-- Prove2me | Definitions.Def_BS2_b3ba934b_RawConditionalBase
-- name    : BS2_b3ba934b_RawConditionalBase
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:28:25.999923+00:00
-- url     : https://prove2.me/theorems/18cb4ec4-40e7-4de2-9b9c-f12502646d1a
-- title:
--   Sensitivity separation: RawConditionalBase (complete source module)
-- statement:
--   Complete Lean source module `RawConditionalBase` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawConditionalBase.lean; original SHA-256 020cfb00e398e59dee9afa9335a39cd3cd3373b4aaa5b87f47823aa9852739d9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Semantic interpretation of numeric entries, ordinary components and raw B. -/
import Definitions.Def_BS2_b3ba934b_OrdinaryParentBridge
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem eval_maximum_three (a b c : Expr n) (v : Profile n) :
    (Expr.maximum [a,b,c]).eval v=max (a.eval v) (max (b.eval v) (c.eval v)) := by
  simp only [Expr.maximum,List.foldr_cons,List.foldr_nil,Expr.eval,Nat.max_zero]

theorem threshold_zero (e : Entry) : e.threshold 0=e.t0 := by simp [Entry.threshold]

theorem ordinary_of_zero (e : Entry) (he : e.tolerance=0) : e.ordinary=true := by
  simp [Entry.ordinary,he]

theorem ordinary_threshold (e : Entry) (he : e.ordinary=true) (d : ℕ)
    (hd : d ≤ e.tolerance) : e.threshold d=e.t0 := by
  simp only [Entry.ordinary,decide_eq_true_eq] at he
  rcases he with he | he | ⟨h01,he | h12⟩
  · simp [Entry.threshold,he]
  · have : d=0 := by omega
    simp [this,threshold_zero]
  · have : d=0 ∨ d=1 := by omega
    rcases this with rfl | rfl <;> simp [Entry.threshold,h01]
  · simp [Entry.threshold,h01,h12]

theorem same_spec (e f : Entry) (he : e.same f=true) :
    e.tolerance=f.tolerance ∧ e.guard=f.guard ∧
      ∀ d, d ≤ e.tolerance → e.threshold d=f.threshold d := by
  simp only [Entry.same,Bool.decide_and,Bool.and_eq_true,decide_eq_true_eq] at he
  rcases he with ⟨hq,hg,ht⟩
  refine ⟨hq,hg,?_⟩
  intro d hd
  have hh := List.all_eq_true.mp ht d (List.mem_range.mpr (by omega))
  simpa only [beq_iff_eq] using hh

/-- Only target values at feasible guard counts are needed for parent equality. -/
theorem parent_eq_ordinary_valid (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (l t : Fin n)
    (hconstant : ∀ d, d ≤ S.tolerance l → ∀ u z,
      S.target l d u z = (F t u && F t z)) :
    parent S F l = ordinaryParent S F t (S.guard l) (S.tolerance l) := by
  funext x
  have hfailed (w : V) : failed S F l x w=guardFailures S F (S.guard l) x w := rfl
  have hi : parent S F l x=true ↔ ordinaryParent S F t (S.guard l) (S.tolerance l) x=true := by
    rw [parent_true_iff,ordinary_parent_true]
    constructor
    · rintro ⟨w,hc,ht⟩
      rw [hconstant _ hc] at ht
      have hh : ∀ c, F t (child x w c)=true := by
        intro c
        cases c <;> simp_all
      exact ⟨w,hh,by simpa only [hfailed] using hc⟩
    · rintro ⟨w,ht,hc⟩
      have hc' : (failed S F l x w).card ≤ S.tolerance l := by simpa only [hfailed] using hc
      refine ⟨w,hc',?_⟩
      rw [hconstant _ hc']
      simp [ht]
  cases h₁ : parent S F l x <;>
    cases h₂ : ordinaryParent S F t (S.guard l) (S.tolerance l) x <;> simp_all

theorem matched_ordinary_weak (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n)
    (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (ha : a.ordinary=true) :
    parent S F i = ordinaryParent S F (P.weak 0) (S.guard i) (S.tolerance i) := by
  apply parent_eq_ordinary_valid
  intro d hd u z
  have ht : P.weak d=P.weak 0 := by
    apply Fin.ext
    rw [hm.weakThreshold,hm.weakThreshold,threshold_zero]
    exact ordinary_threshold a ha d (by simpa only [hm.weakTolerance] using hd)
  rw [P.weakDef,ht]

theorem matched_ordinary_strong (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n)
    (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (hc : c.ordinary=true) :
    parent S F j = ordinaryParent S F (P.strong 0) (S.guard j) (S.tolerance j) := by
  apply parent_eq_ordinary_valid
  intro d hd u z
  have ht : P.strong d=P.strong 0 := by
    apply Fin.ext
    rw [hm.strongThreshold,hm.strongThreshold,threshold_zero]
    exact ordinary_threshold c hc d (by simpa only [hm.strongTolerance] using hd)
  rw [P.strongDef,ht]

theorem matched_same_parent (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (i j : Fin n)
    (P : PairData S F i j) (a c : Entry) (hm : EntryMatch S F i j P a c)
    (hs : a.same c=true) : parent S F i=parent S F j := by
  obtain ⟨hq,hg,ht⟩ := same_spec a c hs
  have hq' : S.tolerance i=S.tolerance j := by rw [hm.weakTolerance,hm.strongTolerance,hq]
  have hg' : S.guard i=S.guard j := Fin.ext (by rw [hm.weakGuard,hm.strongGuard,hg])
  have ht' (d : ℕ) (hd : d ≤ S.tolerance i) : P.weak d=P.strong d := by
    apply Fin.ext
    rw [hm.weakThreshold,hm.strongThreshold]
    exact ht d (by simpa only [hm.weakTolerance] using hd)
  funext x
  have hf (w : V) : failed S F i x w=failed S F j x w := by simp only [failed,hg']
  have hi : parent S F i x=true ↔ parent S F j x=true := by
    rw [parent_true_iff,parent_true_iff]
    constructor
    · rintro ⟨w,hc,hh⟩
      refine ⟨w,by simpa only [← hf,← hq'] using hc,?_⟩
      rw [P.strongDef,← hf,← ht' _ hc,← P.weakDef]
      exact hh
    · rintro ⟨w,hc,hh⟩
      have hc' : (failed S F i x w).card ≤ S.tolerance i := by simpa only [hf,hq'] using hc
      refine ⟨w,hc',?_⟩
      rw [P.weakDef,ht' _ hc',hf,← P.strongDef]
      exact hh
  cases h₁ : parent S F i x <;> cases h₂ : parent S F j x <;> simp_all

/-- Numeric raw B is proved directly from an actual winning graded row. -/
theorem rawBExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (v : Profile n) (hv : Upper F v) :
    BBound (parent S F) i j ((rawBExpr n degree (recipe i) (recipe j)).eval v) := by
  classical
  let t : Fin n → ℕ → Fin n := fun l => if l=i then P.weak else P.strong
  have ti : t i=P.weak := by simp [t]
  have tj : t j=P.strong := by
    by_cases hij : j=i
    · subst j
      have he : P.weak=P.strong := by
        funext d
        exact Fin.ext ((hm.weakThreshold d).trans (hm.strongThreshold d).symm)
      simp [t,he]
    · simp [t,hij]
  intro x hx
  obtain ⟨w,hcount,hwin⟩ := (parent_true_iff S F j x).1 hx
  let d := (failed S F j x w).card
  have hdq : d ≤ S.tolerance j := hcount
  have hstrong : ∀ c, F (P.strong d) (child x w c)=true := by
    rw [P.strongDef,Bool.and_eq_true] at hwin
    intro c
    cases c
    · exact hwin.1
    · exact hwin.2
  let a := (aExpr n (S.guard j).val (S.guard i).val).eval v
  let b := (bExpr n (P.weak d).val (P.strong d).val).eval v
  have ha := aExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb := bExpr_bound F v hv (P.weak d) (P.strong d) (P.targets d hdq)
  have hh := graded_positive_bound S F hF t i j (by simpa only [ti] using P.weakMono)
    P.guards (by simpa only [ti] using P.weakDef) x w d rfl (hdq.trans P.tolerances)
    (by simpa only [ti,tj] using P.targets d hdq) (by simpa only [tj] using hstrong)
    a b ha (by simpa only [ti,tj] using hb)
  rw [ti,tj,hd w] at hh
  have hgate : ((recipe i).tolerance ≤ d ∨ (recipe j).threshold d < (recipe i).threshold (d+1)) ↔
      ¬ (d+1 ≤ S.tolerance i ∧ P.weak (d+1) ≤ P.strong d) := by
    rw [← hm.weakTolerance,← hm.weakThreshold,← hm.strongThreshold]
    change (_ ∨ (P.strong d).val < (P.weak (d+1)).val) ↔ ¬ (_ ∧ (P.weak (d+1)).val ≤ (P.strong d).val)
    omega
  have he : 2*b+(if d+1 ≤ S.tolerance i ∧ P.weak (d+1) ≤ P.strong d then 0 else (degree-d)*a) =
      (2*bExpr n ((recipe i).threshold d) ((recipe j).threshold d)+
        if (recipe i).tolerance ≤ d ∨ (recipe j).threshold d < (recipe i).threshold (d+1)
        then (degree-d)*aExpr n (recipe j).guard (recipe i).guard else 0).eval v := by
    by_cases hs : d+1 ≤ S.tolerance i ∧ P.weak (d+1) ≤ P.strong d
    · rw [if_pos hs,if_neg (by exact fun h => (hgate.mp h) hs)]
      simp only [a,b,hm.weakThreshold,hm.strongThreshold,hm.weakGuard,hm.strongGuard,eval_add,eval_mul,eval_zero]
    · rw [if_neg hs,if_pos (hgate.mpr hs)]
      simp only [a,b,hm.weakThreshold,hm.strongThreshold,hm.weakGuard,hm.strongGuard,eval_add,eval_mul]
  have hh' : (flipsTo (parent S F i) false x).card ≤
      2*b+(if d+1 ≤ S.tolerance i ∧ P.weak (d+1) ≤ P.strong d then 0 else (degree-d)*a) := by
    by_cases hs : d+1 ≤ S.tolerance i ∧ P.weak (d+1) ≤ P.strong d
    · simpa only [if_pos hs] using hh
    · simpa only [if_neg hs] using hh
  apply hh'.trans (he.le.trans ?_)
  simp only [rawBExpr,Expr.eval_maximum,List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  exact ⟨d,List.mem_range.mpr (by rw [← hm.strongTolerance]; omega),rfl⟩

/-- Exact expression interpretation of the improved ordinary-component M bound. -/
theorem primitiveMExpr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk gi gj gk : Fin n) (qi q : ℕ) (j k : Entry)
    (htj : tj.val=j.t0) (htk : tk.val=k.t0) (hgj : gj.val=j.guard) (hgk : gk.val=k.guard)
    (hjq : j.tolerance=q)
    (htij : ti ≤ tj) (htjk : tj ≤ tk) (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hq : q ≤ qi)
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree) (v : Profile n) (hv : Upper F v)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj q x=true) (hxk : ordinaryParent S F tk gk q x=false) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤
      (primitiveMExpr n degree ti.val gi.val qi j k).eval v := by
  have hm := minusExpr_bound_all F hF v hv ti tj tk htij
  have hb := bExpr_bound F v hv ti tk (htij.trans htjk)
  have ha := aExpr_bound F v hv gj gi hgjgi
  have hp := plusExpr_bound_all F hF v hv gk gj gi hgjgi
  have hh := primitiveM S F hF ti tj tk gi gj gk htij htjk hgjgi hgkgj qi q hq
    degree _ _ _ _ hd hm hb ha hp x hxj hxk
  simpa only [primitiveMExpr,← htj,← htk,← hgj,← hgk,hjq,
    eval_max,eval_add,eval_mul,eval_zero,Fin.lt_def,apply_ite] using hh

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawBExpr_bound
#print axioms ThreeBoundConditionalNumeric.primitiveMExpr_bound


