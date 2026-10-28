-- Prove2me | Definitions.Def_BS2_b3ba934b_CachedRawChecker
-- name    : BS2_b3ba934b_CachedRawChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:58:54.510309+00:00
-- url     : https://prove2.me/theorems/29f2b9dc-192a-4241-9c37-ddb7114474ab
-- title:
--   Sensitivity separation: CachedRawChecker (complete source module)
-- statement:
--   Complete Lean source module `CachedRawChecker` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/CachedRawChecker.lean; original SHA-256 4cb1820a38697618ea1e8472aa4127de8d7c6c806248856ec1a9049238dfa09c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_RawBoundChecker

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

structure CostValues where
  heads : Array (Array ℕ)
  guard : ℕ
  negative : Array ℕ

def coeffCheck (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) : Bool :=
  values.heads==computedCosts n v a c &&
  values.guard==(bExpr n c.guard a.guard).eval v &&
  (List.range (c.tolerance+1)).all fun k=>
    values.negative.getD k 0==(aExpr n c.guard (c.threshold k)).eval v

def cachedRecordCost (caps : Caps) (q : ℕ) (values : CostValues) (x : Q2Record) : ℕ :=
  x 8*values.guard+
  ((List.range (q+1)).map fun k=>negativeCount caps q x k*values.negative.getD k 0).sum+
  ((List.range 8).map fun t=>x t*readCost values.heads t 0+
    x (9+2*t)*(readCost values.heads t 1-readCost values.heads t 0)+
    x (10+2*t)*(readCost values.heads t 2-readCost values.heads t 0)).sum

theorem cachedRecordCost_eq (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (values : CostValues) (h : coeffCheck n v a c values=true) (x : Q2Record) :
    cachedRecordCost caps c.tolerance values x=
      recordCostFast n v caps a c (computedCosts n v a c) x := by
  have hparts : values.heads=computedCosts n v a c ∧
      values.guard=(bExpr n c.guard a.guard).eval v ∧
      ∀ k<c.tolerance+1, values.negative.getD k 0=(aExpr n c.guard (c.threshold k)).eval v := by
    simpa [coeffCheck,List.all_eq_true,Nat.lt_succ_iff,and_assoc] using h
  obtain ⟨hh,hg,hn⟩ := hparts
  unfold cachedRecordCost recordCostFast
  rw [hh,hg]
  congr 1
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [hn k (List.mem_range.mp hk)]

def cachedRecordCheck (caps : Caps) (a c : Entry) (values : CostValues)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x:=recordOfList xs
  if recordAllowedFor caps a c x then cachedRecordCost caps c.tolerance values x≤bound else true

def indexedCachedCheck (caps : Caps) (records : List (List ℕ)) (a c : Entry)
    (values : CostValues) (bound k : ℕ) : Bool :=
  cachedRecordCheck caps a c values bound (records[k]?.getD [])

theorem cached_to_record_check (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (values : CostValues) (h : coeffCheck n v a c values=true) (bound : ℕ) (xs : List ℕ) :
    cachedRecordCheck caps a c values bound xs=recordBoundCheck n v caps a c bound xs := by
  simp only [cachedRecordCheck,recordBoundCheck,cachedRecordCost_eq n v caps a c values h]

theorem rawA_le_of_cached_checks (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (values : CostValues) (bound : ℕ)
    (hpos : 0<c.tolerance) (htwo : c.tolerance≤2)
    (hc : coeffCheck n v a c values=true)
    (h : ∀ k, k<records.length → indexedCachedCheck caps records a c values bound k=true) :
    (rawAExpr n caps records a c).eval v≤bound := by
  apply rawA_le_of_indexed_checks n v caps records a c bound hpos htwo
  intro k hk
  have hh:=h k hk
  simpa only [indexedCachedCheck,indexedRecordCheck,
    cached_to_record_check n v caps a c values hc] using hh

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.rawA_le_of_cached_checks


