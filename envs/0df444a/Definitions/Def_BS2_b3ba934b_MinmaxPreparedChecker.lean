-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxPreparedChecker
-- name    : BS2_b3ba934b_MinmaxPreparedChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:27:28.334644+00:00
-- url     : https://prove2.me/theorems/28c07281-663f-4ba2-bbe6-54ed19a5af85
-- title:
--   Sensitivity separation: MinmaxPreparedChecker (complete source module)
-- statement:
--   Complete Lean source module `MinmaxPreparedChecker` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxPreparedChecker.lean; original SHA-256 5c6f89817f9c1b3d561eaecfe3041d3aa847d0621dfb9f57dff1d625168d76c3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Verified coefficient and prepared-record caching for the shared min/max
   numerical transfer. The cached caps are exactly the first endpoint's caps. -/
import Definitions.Def_BS2_b3ba934b_MinmaxAExpressions
import Definitions.Def_BS2_b3ba934b_PreparedRawChecker

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundMinmaxA
open ThreeBoundNumeric ThreeBoundFullProfile

def computedCosts (n : ℕ) (v : Profile n) (a c : ThreeBoundMinmaxNumeric.Entry) : Array (Array ℕ) := #[
  #[(headCost n a c 0 0).eval v,(headCost n a c 0 1).eval v,(headCost n a c 0 2).eval v],
  #[(headCost n a c 1 0).eval v,(headCost n a c 1 1).eval v,(headCost n a c 1 2).eval v],
  #[(headCost n a c 2 0).eval v,(headCost n a c 2 1).eval v,(headCost n a c 2 2).eval v],
  #[(headCost n a c 3 0).eval v,(headCost n a c 3 1).eval v,(headCost n a c 3 2).eval v],
  #[(headCost n a c 4 0).eval v,(headCost n a c 4 1).eval v,(headCost n a c 4 2).eval v],
  #[(headCost n a c 5 0).eval v,(headCost n a c 5 1).eval v,(headCost n a c 5 2).eval v],
  #[(headCost n a c 6 0).eval v,(headCost n a c 6 1).eval v,(headCost n a c 6 2).eval v],
  #[(headCost n a c 7 0).eval v,(headCost n a c 7 1).eval v,(headCost n a c 7 2).eval v]
]

def coeffCheck (n : ℕ) (v : Profile n) (a c : ThreeBoundMinmaxNumeric.Entry)
    (values : CostValues) : Bool :=
  values.heads==computedCosts n v a c &&
  values.guard==(bExpr n c.guard a.guard).eval v &&
  (List.range (c.tolerance+1)).all fun k=>
    values.negative.getD k 0==(aExpr n c.guard (c.lowerAt k)).eval v

def recordCostFast (n : ℕ) (v : Profile n) (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry)
    (costs : Array (Array ℕ)) (x : Q2Record) : ℕ :=
  x 8*(bExpr n c.guard a.guard).eval v+
  ((List.range (c.tolerance+1)).map fun k=>
    negativeCount caps c.tolerance x k*(aExpr n c.guard (c.lowerAt k)).eval v).sum+
  ((List.range 8).map fun t=>x t*readCost costs t 0+
    x (9+2*t)*(readCost costs t 1-readCost costs t 0)+
    x (10+2*t)*(readCost costs t 2-readCost costs t 0)).sum

theorem recordCostFast_eq (n : ℕ) (v : Profile n) (caps : Caps)
    (a c : ThreeBoundMinmaxNumeric.Entry) (x : Q2Record) :
    recordCostFast n v caps a c (computedCosts n v a c) x=(recordCost n caps a c x).eval v := by
  simp only [recordCostFast,recordCost,negativeExpr,highExpr,Expr.eval,Expr.eval_sum,List.map_map]
  congr 1

theorem cachedRecordCost_eq (n : ℕ) (v : Profile n) (caps : Caps)
    (a c : ThreeBoundMinmaxNumeric.Entry) (values : CostValues)
    (h : coeffCheck n v a c values=true) (x : Q2Record) :
    cachedRecordCost caps c.tolerance values x=(recordCost n caps a c x).eval v := by
  have hparts : values.heads=computedCosts n v a c ∧
      values.guard=(bExpr n c.guard a.guard).eval v ∧
      ∀ k<c.tolerance+1, values.negative.getD k 0=(aExpr n c.guard (c.lowerAt k)).eval v := by
    simpa [coeffCheck,List.all_eq_true,Nat.lt_succ_iff,and_assoc] using h
  obtain ⟨hh,hg,hn⟩ := hparts
  rw [← recordCostFast_eq]
  unfold cachedRecordCost recordCostFast
  rw [hh,hg]
  congr 1
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [hn k (List.mem_range.mp hk)]

def recordStateAllowed (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) : Bool :=
  (List.range (c.tolerance+1)).all (fun b =>
      !(b<a.tolerance ∧ a.lowerAt (b+1)≤c.lowerAt b ∧ a.upperAt (b+1)≤c.upperAt b) ||
        (r (3+b)==0 && (if b=0 then r 6==0 else if b=1 then r 7==0 else true))) &&
    (List.range (c.tolerance+1)).all (fun b =>
      r b==0 || !(c.guard==a.lowerAt b && c.guard==a.upperAt b))

theorem recordAllowed_factor (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry) (x : Q2Record) :
    recordAllowedFor caps a c x=(allowedRecord caps c.tolerance x && recordStateAllowed a c x) := by
  simp only [recordAllowedFor,recordStateAllowed,Bool.and_assoc]

def preparedRecordCheck (a c : ThreeBoundMinmaxNumeric.Entry) (p : PreparedValues)
    (values : CostValues) (bound : ℕ) (xs : List ℕ) : Bool :=
  let x:=recordOfList xs
  if p.feasible && recordStateAllowed a c x then preparedCost c.tolerance p values x≤bound else true

def indexedPreparedCheck (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : ThreeBoundMinmaxNumeric.Entry) (values : CostValues) (bound k : ℕ) : Bool :=
  preparedRecordCheck a c (pre k) values bound (table.get k)

theorem record_bound_of_prepared (n : ℕ) (v : Profile n) (caps : Caps)
    (a c : ThreeBoundMinmaxNumeric.Entry) (p : PreparedValues) (values : CostValues)
    (bound : ℕ) (xs : List ℕ)
    (hp : PreparedOK caps c.tolerance (recordOfList xs) p)
    (hc : coeffCheck n v a c values=true)
    (h : preparedRecordCheck a c p values bound xs=true)
    (ha : recordAllowedFor caps a c (recordOfList xs)=true) :
    (recordCost n caps a c (recordOfList xs)).eval v≤bound := by
  rw [recordAllowed_factor,← hp.1] at ha
  have hf : p.feasible=true := by
    have hh := ha
    simp only [Bool.and_eq_true] at hh
    exact hh.1
  have hh : preparedCost c.tolerance p values (recordOfList xs)≤bound := by
    simpa only [preparedRecordCheck,ha,if_true,decide_eq_true_eq] using h
  rw [preparedCost_eq caps c.tolerance p values (recordOfList xs) hp hf,
    cachedRecordCost_eq n v caps a c values hc] at hh
  exact hh

theorem gradedA_le_of_prepared_checks (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : ThreeBoundMinmaxNumeric.Entry) (values : CostValues) (bound : ℕ)
    (hvalid : table.valid) (hrows : table.rows=records)
    (hc : coeffCheck n v a c values=true)
    (hp : ∀ k, k<table.rows.length → PreparedOK caps c.tolerance (recordOfList (table.get k)) (pre k))
    (h : ∀ k, k<table.rows.length → indexedPreparedCheck table pre a c values bound k=true) :
    (gradedAExpr n caps records a c).eval v≤bound := by
  rw [gradedAExpr,Expr.eval_maximum]
  apply maximum_le
  intro value hv
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
  obtain ⟨xs,hxs,he⟩ := List.mem_filterMap.mp he
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hxs
  have hlen : k.val<table.rows.length := by simpa only [hrows] using k.isLt
  have heq : table.get k.val=xs := by
    rw [table.get_correct hvalid k.val hlen,hrows,List.getElem?_eq_getElem k.isLt]
    exact hk
  have hp' := hp k.val hlen
  have h' := h k.val hlen
  rw [heq] at hp'
  change preparedRecordCheck a c (pre k.val) values bound (table.get k.val)=true at h'
  rw [heq] at h'
  by_cases ha : recordAllowedFor caps a c (recordOfList xs)=true
  · simp only [ha,if_true] at he
    have he' : recordCost n caps a c (recordOfList xs)=e := Option.some.inj he
    rw [← he']
    exact record_bound_of_prepared n v caps a c (pre k.val) values bound xs hp' hc h' ha
  · simp [ha] at he

theorem rawA_le_graded (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hplain : (a.plain && c.plain)=false) (hpos : c.tolerance≠0) :
    (rawAExpr n caps records a c).eval v≤(gradedAExpr n caps records a c).eval v := by
  simp only [rawAExpr,hplain,Bool.false_eq_true,if_false,hpos]
  by_cases ho : c.ordinary=true
  · simp only [ho,if_true,Expr.eval_minimum]
    exact foldl_min_le _ _
  · simp only [ho,if_false]
    exact le_rfl

theorem rawA_le_of_prepared_checks (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : ThreeBoundMinmaxNumeric.Entry) (values : CostValues) (bound : ℕ)
    (hvalid : table.valid) (hrows : table.rows=records)
    (hplain : (a.plain && c.plain)=false) (hpos : c.tolerance≠0)
    (hc : coeffCheck n v a c values=true)
    (hp : ∀ k, k<table.rows.length → PreparedOK caps c.tolerance (recordOfList (table.get k)) (pre k))
    (h : ∀ k, k<table.rows.length → indexedPreparedCheck table pre a c values bound k=true) :
    (rawAExpr n caps records a c).eval v≤bound :=
  (rawA_le_graded n v caps records a c hplain hpos).trans
    (gradedA_le_of_prepared_checks n v caps records table pre a c values bound hvalid hrows hc hp h)

end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.rawA_le_of_prepared_checks


