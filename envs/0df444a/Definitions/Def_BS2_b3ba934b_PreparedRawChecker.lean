-- Prove2me | Definitions.Def_BS2_b3ba934b_PreparedRawChecker
-- name    : BS2_b3ba934b_PreparedRawChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:01:55.321614+00:00
-- url     : https://prove2.me/theorems/c4be814b-9f86-415b-8d2a-98e02eb67ab4
-- title:
--   Sensitivity separation: PreparedRawChecker (complete source module)
-- statement:
--   Complete Lean source module `PreparedRawChecker` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/PreparedRawChecker.lean; original SHA-256 48d41645deba94349602164ef88f37bbcc01c726df185bb5d88d6740cb8ef1a2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Reuse the exact record cap computation across all recipe pairs. -/
import Definitions.Def_BS2_b3ba934b_RecordLookup

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric

structure PreparedValues where
  feasible : Bool
  negative : Array ℕ

def PreparedOK (caps : Caps) (q : ℕ) (x : Q2Record) (p : PreparedValues) : Prop :=
  p.feasible=allowedRecord caps q x ∧
    (p.feasible=true → ∀ k : Fin (q+1), p.negative.getD k.val 0=negativeCount caps q x k.val)

instance (caps : Caps) (q : ℕ) (x : Q2Record) (p : PreparedValues) :
    Decidable (PreparedOK caps q x p) := by unfold PreparedOK; infer_instance

def recordStateAllowed (a c : Entry) (x : Q2Record) : Bool :=
  (List.range (c.tolerance+1)).all (fun k =>
      !(k<a.tolerance ∧ a.threshold (k+1)≤c.threshold k) ||
        (x (3+k)==0 && (if k=0 then x 6==0 else if k=1 then x 7==0 else true))) &&
    (List.range (c.tolerance+1)).all (fun k => x k==0 ||
      !(c.guard==(if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))))

theorem recordAllowed_factor (caps : Caps) (a c : Entry) (x : Q2Record) :
    recordAllowedFor caps a c x=(allowedRecord caps c.tolerance x && recordStateAllowed a c x) := by
  simp only [recordAllowedFor,recordStateAllowed,Bool.and_assoc]

def preparedCost (q : ℕ) (p : PreparedValues) (values : CostValues) (x : Q2Record) : ℕ :=
  x 8*values.guard+
  ((List.range (q+1)).map fun k=>p.negative.getD k 0*values.negative.getD k 0).sum+
  ((List.range 8).map fun t=>x t*readCost values.heads t 0+
    x (9+2*t)*(readCost values.heads t 1-readCost values.heads t 0)+
    x (10+2*t)*(readCost values.heads t 2-readCost values.heads t 0)).sum

theorem preparedCost_eq (caps : Caps) (q : ℕ) (p : PreparedValues)
    (values : CostValues) (x : Q2Record) (h : PreparedOK caps q x p) (hf : p.feasible=true) :
    preparedCost q p values x=cachedRecordCost caps q values x := by
  unfold preparedCost cachedRecordCost
  congr 1
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [h.2 hf ⟨k,List.mem_range.mp hk⟩]

def preparedRecordCheck (a c : Entry) (p : PreparedValues) (values : CostValues)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x:=recordOfList xs
  if p.feasible && recordStateAllowed a c x then preparedCost c.tolerance p values x≤bound else true

theorem prepared_to_cached (caps : Caps) (a c : Entry) (p : PreparedValues)
    (values : CostValues) (bound : ℕ) (xs : List ℕ)
    (h : PreparedOK caps c.tolerance (recordOfList xs) p) :
    preparedRecordCheck a c p values bound xs=cachedRecordCheck caps a c values bound xs := by
  have heq:=h.1
  by_cases hf : p.feasible=true
  · simp only [preparedRecordCheck,cachedRecordCheck,recordAllowed_factor,← heq,
      preparedCost_eq caps c.tolerance p values (recordOfList xs) h hf]
  · have hf' : p.feasible=false := Bool.eq_false_of_not_eq_true hf
    simp only [preparedRecordCheck,cachedRecordCheck,recordAllowed_factor,← heq,hf',Bool.false_and,
      Bool.false_eq_true,if_false]

def indexedPreparedCheck (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : Entry) (values : CostValues) (bound k : ℕ) : Bool :=
  preparedRecordCheck a c (pre k) values bound (table.get k)

theorem rawA_le_of_prepared_checks (n : ℕ) (v : ThreeBoundFullProfile.Profile n) (caps : Caps)
    (records : List (List ℕ)) (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : Entry) (values : CostValues) (bound : ℕ)
    (hvalid : table.valid) (hrows : table.rows=records)
    (hpos : 0<c.tolerance) (htwo : c.tolerance≤2)
    (hc : coeffCheck n v a c values=true)
    (hp : ∀ k, k<table.rows.length → PreparedOK caps c.tolerance (recordOfList (table.get k)) (pre k))
    (h : ∀ k, k<table.rows.length → indexedPreparedCheck table pre a c values bound k=true) :
    (rawAExpr n caps records a c).eval v≤bound := by
  apply rawA_le_of_fast_checks n v caps records table a c values bound hvalid hrows hpos htwo hc
  intro k hk
  have hh:=h k hk
  simpa only [indexedPreparedCheck,indexedFastCachedCheck,prepared_to_cached caps a c (pre k)
    values bound (table.get k) (hp k hk)] using hh

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.rawA_le_of_prepared_checks


