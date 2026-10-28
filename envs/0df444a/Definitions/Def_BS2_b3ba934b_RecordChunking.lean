-- Prove2me | Definitions.Def_BS2_b3ba934b_RecordChunking
-- name    : BS2_b3ba934b_RecordChunking
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:49:08.560675+00:00
-- url     : https://prove2.me/theorems/3c7150cb-7b6d-4ff7-bcad-4dcca4fbf6df
-- title:
--   Sensitivity separation: RecordChunking (complete source module)
-- statement:
--   Complete Lean source module `RecordChunking` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecordChunking.lean; original SHA-256 2e3bc9e8cc2dc604b6e711bf235c3b6294700cf8612dec7e45e019a90f1547c3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Composition of bounded exhaustive-enumeration checks. -/
import Definitions.Def_BS2_b3ba934b_RecordSetLookup
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false

namespace ThreeBoundRecordLookup

def checkFrom (tree : Tree) (n start : ℕ) : Bool :=
  ((ThreeBoundQ2.typeLists 0 n).drop start).all (checkTypes tree)

theorem checkFrom_step (tree : Tree) (n start count : ℕ)
    (hleft : checkChunk tree n start count=true)
    (hright : checkFrom tree n (start+count)=true) :
    checkFrom tree n start=true := by
  unfold checkFrom
  rw [← List.take_append_drop count ((ThreeBoundQ2.typeLists 0 n).drop start),
    List.all_append]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hleft,?_⟩
  simpa only [List.drop_drop,Nat.add_comm,checkFrom] using hright

theorem checkFrom_end (tree : Tree) (n start : ℕ)
    (hlen : (ThreeBoundQ2.typeLists 0 n).length≤start) :
    checkFrom tree n start=true := by
  simp only [checkFrom,List.drop_eq_nil_of_le hlen,List.all_nil]

theorem checkLength_of_from (tree : Tree) (n : ℕ)
    (h : checkFrom tree n 0=true) : checkLength tree n=true := by
  simpa only [checkFrom,List.drop_zero,checkLength] using h

def activeTypes (n : ℕ) : List (List ThreeBoundQ2.Kind) :=
  (ThreeBoundQ2.typeLists 0 n).filter fun ts => decide (ThreeBoundQ2.allowedTypes ts)

theorem checkLength_of_active (tree : Tree) (n : ℕ)
    (h : (activeTypes n).all (checkTypes tree)=true) : checkLength tree n=true := by
  apply List.all_eq_true.mpr
  intro ts hts
  by_cases ha : ThreeBoundQ2.allowedTypes ts
  · exact List.all_eq_true.mp h ts (List.mem_filter.mpr ⟨hts,by simpa using ha⟩)
  · simp [checkTypes,ThreeBoundQ2.casesFor,ha]

def checkCasesChunk (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start count : ℕ) : Bool :=
  (((ThreeBoundQ2.casesFor ts).drop start).take count).all fun c => tree.contains (recordFast c)

def checkCasesFrom (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start : ℕ) : Bool :=
  ((ThreeBoundQ2.casesFor ts).drop start).all fun c => tree.contains (recordFast c)

theorem checkCasesFrom_step (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start count : ℕ)
    (hleft : checkCasesChunk tree ts start count=true)
    (hright : checkCasesFrom tree ts (start+count)=true) :
    checkCasesFrom tree ts start=true := by
  unfold checkCasesFrom
  rw [← List.take_append_drop count ((ThreeBoundQ2.casesFor ts).drop start),List.all_append]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hleft,?_⟩
  simpa only [List.drop_drop,Nat.add_comm,checkCasesFrom] using hright

theorem checkCasesFrom_end (tree : Tree) (ts : List ThreeBoundQ2.Kind) (start : ℕ)
    (hlen : (ThreeBoundQ2.casesFor ts).length≤start) : checkCasesFrom tree ts start=true := by
  simp only [checkCasesFrom,List.drop_eq_nil_of_le hlen,List.all_nil]

theorem checkTypes_of_from (tree : Tree) (ts : List ThreeBoundQ2.Kind)
    (h : checkCasesFrom tree ts 0=true) : checkTypes tree ts=true := by
  simpa only [checkCasesFrom,List.drop_zero,checkTypes] using h

theorem all_cons_of {α : Type} (p : α → Bool) (a : α) (as : List α)
    (ha : p a=true) (has : as.all p=true) : (a::as).all p=true := by
  simp only [List.all_cons,ha,has,Bool.and_self]

end ThreeBoundRecordLookup


