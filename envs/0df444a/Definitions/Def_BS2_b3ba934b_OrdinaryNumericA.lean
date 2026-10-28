-- Prove2me | Definitions.Def_BS2_b3ba934b_OrdinaryNumericA
-- name    : BS2_b3ba934b_OrdinaryNumericA
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:33:40.554994+00:00
-- url     : https://prove2.me/theorems/16167547-b1d9-4f6a-a3f3-634d76ee7391
-- title:
--   Sensitivity separation: OrdinaryNumericA (complete source module)
-- statement:
--   Complete Lean source module `OrdinaryNumericA` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/OrdinaryNumericA.lean; original SHA-256 96da74699b874c6b0723044bea042648cd1594ddbaf3965caa4499ffc93d8b50; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Ordinary raw-A expression semantics and the exact ordinary components
of a graded weak parent. -/
import Definitions.Def_BS2_b3ba934b_OrdinaryNumericCases

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

theorem eval_maximum_seven (a b c d e f g : Expr n) (v : Profile n) :
    (Expr.maximum [a,b,c,d,e,f,g]).eval v=
      max (a.eval v) (max (b.eval v) (max (c.eval v) (max (d.eval v)
        (max (e.eval v) (max (f.eval v) (g.eval v)))))) := by
  simp only [Expr.maximum,List.foldr_cons,List.foldr_nil,Expr.eval,Nat.max_zero]

theorem ordinaryAExpr_zero_equal (v : Profile n) (ta ga tb gb : ℕ) :
    (ordinaryAExpr n ordinaryCaps10007 ta ga 0 tb gb 0).eval v=
      ThreeBoundOrdinaryArchive.ZT.zeroCost
        ((plusExpr n gb ta tb).eval v) ((aExpr n gb tb).eval v)
        ((bExpr n gb ga).eval v) ((bExpr n gb tb).eval v)
        ((unionExpr n gb ga ta tb).eval v) := by
  simp only [ordinaryAExpr,ite_true,ne_eq,not_true_eq_false,ite_false,
    eval_maximum_seven,eval_add,eval_mul,eval_min,eval_max,
    ThreeBoundOrdinaryArchive.ZT.zeroCost,max_assoc]
  rfl

theorem ordinaryAExpr_zero_strict (v : Profile n) (ta ga qa tb gb : ℕ) (hqa : qa ≠ 0) :
    (ordinaryAExpr n ordinaryCaps10007 ta ga qa tb gb 0).eval v=
      max (22*((aExpr n gb tb).eval v))
        (((plusExpr n gb ta tb).eval v)+19*((aExpr n gb tb).eval v)) := by
  simp only [ordinaryAExpr,ite_true,if_pos hqa,eval_add,eval_mul,eval_max]
  rfl

/-- Full ordinary transfer with semantic child bounds only. The temporary
min(j,s) enforces the cost proof's order requirement without constraining v. -/
theorem ordinaryAExpr_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (qa q : ℕ) (hq : q ≤ qa) (hq8 : q ≤ 8)
    (v : Profile n) (hv : Upper F v)
    (x : ((Fin 10007 × Bool) × I) → Bool)
    (hx : ordinaryParent S F ta ga qa x=false) :
    (flipsTo (ordinaryParent S F tb gb q) true x).card ≤
      (ordinaryAExpr n ordinaryCaps10007 ta.val ga.val qa tb.val gb.val q).eval v := by
  let a := (plusExpr n gb.val ta.val tb.val).eval v
  let b := (aExpr n gb.val tb.val).eval v
  let s := (bExpr n gb.val ga.val).eval v
  let j := (bExpr n gb.val tb.val).eval v
  let d := (unionExpr n gb.val ga.val ta.val tb.val).eval v
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have ha := plusExpr_bound_all F hF v hv gb ta tb ht
  have hb := aExpr_bound F v hv gb tb hgt
  have hs := bExpr_bound F v hv gb ga hg
  have hj := bExpr_bound F v hv gb tb hgt
  have hd := unionExpr_bound_all F hF v hv gb ga ta tb hg ht
  have hj' : BBound F gb tb (min j s) := b_min F gb tb j s hj
    (b_condition_strengthen F hF gb ga tb (hga.trans ht) s hs)
  by_cases hzero : q=0
  · subst q
    by_cases hqa : qa=0
    · subst qa
      have hh := ordinary_zero_equal_bound S hAdj hLabel F hF ta tb ga gb ht hg hga
        a b s (min j s) d (min_le_right _ _) ha hb hs hj' hd x hx
      apply hh.trans
      rw [ordinaryAExpr_zero_equal]
      exact zeroCost_mono_j a b s (min j s) j d (min_le_left _ _)
    · have hh := ordinary_zero_strict_bound S hAdj hLabel F hF ta tb ga gb ht hg hga
        qa (by omega) a b ha hb x hx
      rw [ordinaryAExpr_zero_strict v _ _ _ _ _ hqa]
      exact hh
  · have hpos : 0<q := by omega
    apply ordinary_positive_bound S hAdj hLabel F hF ta tb ga gb ht hg hga qa q hq hpos hq8
      a b s (min j s) _ (min_le_right _ _) ha hb hs hj' (x:=x) (hx:=hx)
    intro m u hm hu hc hcap hskip
    exact (positiveCaseCost_mono_j q m u a b s (min j s) j (min_le_left _ _)).trans
      (ordinaryAExpr_case_bound v ta.val ga.val qa tb.val gb.val q m u hpos hq8 hm hu hc hcap
        (fun hu he => hskip hu (Fin.ext he)))

/-- Any valid weak budget gives a genuine ordinary component. This is the
ordinary fallback used inside the min for q=1 or q=2. -/
theorem ordinaryComponentAExpr_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (level : ℕ) (hlevel : level ≤ (recipe i).tolerance)
    (hq : (recipe j).tolerance ≤ level) (hq8 : (recipe j).tolerance ≤ 8)
    (hthreshold : (recipe i).threshold level ≤ (recipe j).t0)
    (hordinary : (recipe j).ordinary=true) (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j
      ((ordinaryAExpr n ordinaryCaps10007 ((recipe i).threshold level) (recipe i).guard level
        (recipe j).t0 (recipe j).guard (recipe j).tolerance).eval v) := by
  intro x hx
  have hlevel' : level ≤ S.tolerance i := by simpa only [hm.weakTolerance] using hlevel
  have hq' : S.tolerance j ≤ level := by simpa only [hm.strongTolerance] using hq
  have ht : P.weak level ≤ P.strong 0 := by
    change (P.weak level).val ≤ (P.strong 0).val
    simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero] using hthreshold
  have hcomp : ordinaryParent S F (P.weak level) (S.guard i) level x=false := by
    cases he : ordinaryParent S F (P.weak level) (S.guard i) level x with
    | false => rfl
    | true =>
        have hh := ordinary_component_accepts S F hF (fun _ => P.weak) i
          (P.weak level) (S.guard i) level le_rfl hlevel' (fun d hd => P.weakMono hd) P.weakDef x he
        rw [hx] at hh
        contradiction
  have hh := ordinaryAExpr_bound S hAdj hLabel F hF (P.weak level) (P.strong 0)
    (S.guard i) (S.guard j) ht P.guards (P.weakGuardTarget level hlevel') level (S.tolerance j)
    hq' (by simpa only [hm.strongTolerance] using hq8) v hv x hcomp
  rw [matched_ordinary_strong S F i j P (recipe i) (recipe j) hm hordinary]
  simpa only [hm.weakThreshold,hm.strongThreshold,threshold_zero,hm.weakGuard,hm.strongGuard,hm.strongTolerance] using hh

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.ordinaryAExpr_bound
#print axioms ThreeBoundConditionalNumeric.ordinaryComponentAExpr_bound


