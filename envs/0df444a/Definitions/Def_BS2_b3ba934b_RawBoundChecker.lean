-- Prove2me | Definitions.Def_BS2_b3ba934b_RawBoundChecker
-- name    : BS2_b3ba934b_RawBoundChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:29:21.597117+00:00
-- url     : https://prove2.me/theorems/778d3f3a-18af-4ba3-a089-449ca92e25bb
-- title:
--   Sensitivity separation: RawBoundChecker (complete source module)
-- statement:
--   Complete Lean source module `RawBoundChecker` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawBoundChecker.lean; original SHA-256 eef3ec6945a7a5b72aecc0f7018f065cd2f856bde07963297a30f4f3a2c1960a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Bounded exact checks for a raw q2 maximum. Every record is covered by its
index in the supplied finite list. Chunking changes proof evaluation cost,
not the mathematical maximum or its semantic assumptions. -/
import Definitions.Def_BS2_b3ba934b_Q2FastEvaluator
import Definitions.Def_BS2_b3ba934b_ClosureCertificate

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

theorem foldl_min_le (xs : List ℕ) (v : ℕ) : xs.foldl Nat.min v≤v := by
  induction xs generalizing v with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (min v x)).trans (min_le_left _ _)

def recordBoundCheck (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x := recordOfList xs
  if recordAllowedFor caps a c x then
    recordCostFast n v caps a c (computedCosts n v a c) x≤bound
  else true

def indexedRecordCheck (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (bound k : ℕ) : Bool :=
  recordBoundCheck n v caps a c bound (records[k]?.getD [])

theorem record_check_of_indexed (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (bound : ℕ)
    (h : ∀ k, k<records.length → indexedRecordCheck n v caps records a c bound k=true) :
    ∀ xs ∈ records, recordBoundCheck n v caps a c bound xs=true := by
  intro xs hxs
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hxs
  have heq : records[k.val]?.getD []=xs := by
    rw [List.getElem?_eq_getElem k.isLt]
    exact hk
  have hh := h k.val k.isLt
  simpa only [indexedRecordCheck,heq] using hh

def recordMaximum (n : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (a c : Entry) : ℕ :=
  let costs := computedCosts n v a c
  maximum (records.filterMap fun xs=>
    let x := recordOfList xs
    if recordAllowedFor caps a c x then some (recordCostFast n v caps a c costs x) else none)

theorem recordMaximum_le_of_checks (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (bound : ℕ)
    (h : ∀ xs ∈ records, recordBoundCheck n v caps a c bound xs=true) :
    recordMaximum n v caps records a c≤bound := by
  apply maximum_le
  intro value hv
  obtain ⟨xs,hxs,hvalue⟩ := List.mem_filterMap.mp hv
  have hc := h xs hxs
  dsimp only at hvalue
  by_cases ha : recordAllowedFor caps a c (recordOfList xs)=true
  · simp only [ha,if_true] at hvalue
    have heq : recordCostFast n v caps a c (computedCosts n v a c) (recordOfList xs)=value :=
      Option.some.inj hvalue
    have hle : recordCostFast n v caps a c (computedCosts n v a c) (recordOfList xs)≤bound := by
      simpa [recordBoundCheck,ha] using hc
    simpa only [heq] using hle
  · simp [ha] at hvalue

theorem rawAFast_le_recordMaximum (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (hpos : 0<c.tolerance) (htwo : c.tolerance≤2) :
    rawAFast n v caps records a c≤recordMaximum n v caps records a c := by
  have h0 : c.tolerance≠0 := by omega
  have h3 : ¬3≤c.tolerance := by omega
  simp only [rawAFast,h0,h3,if_false,recordMaximum]
  by_cases ho : c.ordinary=true
  · simp only [ho,if_true]
    exact foldl_min_le _ _
  · simp only [ho,if_false]
    exact le_rfl

theorem rawA_le_of_indexed_checks (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (bound : ℕ)
    (hpos : 0<c.tolerance) (htwo : c.tolerance≤2)
    (h : ∀ k, k<records.length → indexedRecordCheck n v caps records a c bound k=true) :
    (rawAExpr n caps records a c).eval v≤bound := by
  rw [← rawAFast_eq]
  exact (rawAFast_le_recordMaximum n v caps records a c hpos htwo).trans
    (recordMaximum_le_of_checks n v caps records a c bound
      (record_check_of_indexed n v caps records a c bound h))

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.rawA_le_of_indexed_checks


