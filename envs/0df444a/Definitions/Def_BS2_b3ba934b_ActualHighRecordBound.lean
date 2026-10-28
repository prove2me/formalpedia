-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualHighRecordBound
-- name    : BS2_b3ba934b_ActualHighRecordBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:10:41.193985+00:00
-- url     : https://prove2.me/theorems/de476a52-6333-4b28-be77-b5ad6160a59f
-- title:
--   Sensitivity separation: ActualHighRecordBound (complete source module)
-- statement:
--   Complete Lean source module `ActualHighRecordBound` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualHighRecordBound.lean; original SHA-256 a788f758a8df0c9aa437911ba5cbdfd0bed7ee6207c4a4de779231f1f3121240; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The high-head and external-arc parts of the exact record cost bound actual
   parent flip sets, with no semantic transfer assumption. -/
import Definitions.Def_BS2_b3ba934b_ActualRecordFields
import Definitions.Def_BS2_b3ba934b_HeadCostOrder

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHighRecordBound
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundActualRecordFields
open ThreeBoundHeadCostOrder ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundQ2
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def highExpr (n : ℕ) (a c : Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range 8).map fun t =>
    r t * headCost n a c t 0 +
    r (9+2*t) * (headCost n a c t 1-headCost n a c t 0) +
    r (10+2*t) * (headCost n a c t 2-headCost n a c t 0))

theorem sum_range_eight (f : ℕ → ℕ) :
    ((List.range 8).map f).sum = ∑ k : Fin 8, f k.val := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,Fin.val_one]
  norm_num only [Nat.reduceAdd]
  omega

theorem eval_sub (v : Profile n) (a b : Expr n) : (a-b).eval v = a.eval v-b.eval v := rfl

theorem highExpr_eval (a c : Entry) (r : Q2Record) (v : Profile n) :
    (highExpr n a c r).eval v = ∑ k : Kind,
      (r k.val * (headCost n a c k.val 0).eval v +
       r (9+2*k.val) * ((headCost n a c k.val 1).eval v-(headCost n a c k.val 0).eval v) +
       r (10+2*k.val) * ((headCost n a c k.val 2).eval v-(headCost n a c k.val 0).eval v)) := by
  rw [highExpr,Expr.eval_sum,List.map_map,sum_range_eight]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply,ThreeBoundHeadCostOrder.eval_add,
    ThreeBoundHeadCostOrder.eval_scale,ThreeBoundHighRecordBound.eval_sub]

theorem highBits_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (hQ : S.tolerance j ≤ 2)
    (tag : V → Kind)
    (htag : ∀ w ∈ highHeads S F P.strong j x,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
        (child x w false) (child x w true) (tag w))
    (r : Q2Record)
    (htypes : ∀ k : Kind, r k.val =
      ((highHeads S F P.strong j x).filter fun w => tag w = k).card)
    (hhist : ∀ (k : Kind) (h : Fin 2), r (9+2*k.val+h.val) =
      ((highHeads S F P.strong j x).filter fun w => tag w = k ∧
        min 2 (incomingSources S F P.strong j x w).card = h.val+1).card) :
    (highBits S F P.strong j x).card ≤ (highExpr n a c r).eval v := by
  let H := highHeads S F P.strong j x
  let inc := fun w => (incomingSources S F P.strong j x w).card
  let sets := fun w => headBits w (actualHeadParts S F P.strong j x w)
  let cost := fun k : Kind => fun h => (headCost n a c k.val h).eval v
  have hcost : ∀ w ∈ H, (sets w).card ≤ cost (tag w) (min 2 (inc w)) := by
    intro w hw
    exact actual_kind_headCost_bound S F hF i j P a c matchE v hv x hoff hQ w (tag w) (htag w hw)
  have hb := ThreeBoundAccounting.histogram_delta_bound H tag inc sets cost hcost
    (fun k => headCost_zero_le a c v k 1) (fun k => headCost_zero_le a c v k 2)
  letI : DecidableEq ((V × Bool) × I) := fun a b => Classical.propDecidable (a=b)
  have heHigh : highBits S F P.strong j x = H.biUnion sets := by
    ext bit
    simp only [highBits,H,sets,Finset.mem_biUnion]
  rw [heHigh]
  apply hb.trans_eq
  rw [highExpr_eval]
  apply Finset.sum_congr rfl
  intro k _
  have hh1 := hhist k 0
  have hh2 := hhist k 1
  have hindex : 9+2*k.val+1 = 10+2*k.val := by omega
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero,zero_add,hindex,Nat.reduceAdd] at hh1 hh2
  have ht0 : ThreeBoundAccounting.typeCount H tag k = r k.val := by
    unfold ThreeBoundAccounting.typeCount
    convert (htypes k).symm using 1 <;> congr 1 <;> ext w <;> simp [H]
  have ht1 : ThreeBoundAccounting.hist H tag inc k 1 = r (9+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh1.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  have ht2 : ThreeBoundAccounting.hist H tag inc k 2 = r (10+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh2.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  rw [ht0,ht1,ht2]

theorem externalBits_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (r : Q2Record)
    (hext : r 8 = ∑ w ∈ guardSources S F P.strong j x,
      ((failed S F j x w).card-((highHeads S F P.strong j x).filter (S.Adj w)).card)) :
    (ThreeBoundGradedCover.externalBits S F P.strong j x).card ≤
      (r 8 * bExpr n c.guard a.guard).eval v := by
  have hs := bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb := ThreeBoundAccounting.externalBits_card_le S F i j x
    (guardSources S F P.strong j x) (highHeads S F P.strong j x)
    (high_guards_true S F hF i j P x)
    (guard_source_weak_eligibility S F hF i j P x hoff) _ hs
  change (ThreeBoundGradedCover.externalBits S F P.strong j x).card ≤ _ at hb
  rw [← hext,matchE.strongGuard,matchE.weakGuard] at hb
  exact hb

/-- End-to-end interpretation of both record terms for the actual numbering
    produced by the complete q2 enumerator. -/
theorem actual_record_high_external
    (S : Stage (Fin n) I V) (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (hQ : S.tolerance j ≤ 2)
    (tag : V → Kind)
    (htag : ∀ w ∈ highHeads S F P.strong j x,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
        (child x w false) (child x w true) (tag w))
    (hcount : ∀ w ∈ highHeads S F P.strong j x,
      (failed S F j x w).card = ThreeBoundQ2.budget (tag w))
    (ts : List Kind) (ds : List Bool) (e : Fin ts.length ≃ highHeads S F P.strong j x)
    (hget : ∀ k, ts.get k = tag (e k).val)
    (hdirs : ds = orientationBits (fun k l => S.Adj (e k).val (e l).val)) :
    let r := recordOfList (record (ts,ds))
    (highBits S F P.strong j x).card ≤ (highExpr n a c r).eval v ∧
    (ThreeBoundGradedCover.externalBits S F P.strong j x).card ≤
      (r 8 * bExpr n c.guard a.guard).eval v := by
  let H := highHeads S F P.strong j x
  let G := guardSources S F P.strong j x
  have hG : G = H.filter fun w => isGuard (tag w) = true :=
    guardSources_eq_filter S F P.strong j x tag htag
  obtain ⟨htypes,hext,hhist,_⟩ := all_record_fields ts ds H G tag S.Adj hR e hget hdirs hG
    (fun w => (failed S F j x w).card) hcount
  dsimp only
  constructor
  · apply highBits_expr_bound S F hF i j P a c matchE v hv x hoff hQ tag htag
      (recordOfList (record (ts,ds))) htypes
    intro kind hits
    convert hhist kind hits using 1 <;> congr 1 <;> ext w <;> simp [H,G,incomingSources]
  · exact externalBits_expr_bound S F hF i j P a c matchE v hv x hoff _ hext

end
end ThreeBoundHighRecordBound

#print axioms ThreeBoundHighRecordBound.highBits_expr_bound
#print axioms ThreeBoundHighRecordBound.externalBits_expr_bound
#print axioms ThreeBoundHighRecordBound.actual_record_high_external


