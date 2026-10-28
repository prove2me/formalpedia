-- Prove2me | Definitions.Def_BS2_b3ba934b_RecordSetLookup
-- name    : BS2_b3ba934b_RecordSetLookup
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:47:17.022096+00:00
-- url     : https://prove2.me/theorems/2d085af2-80ae-4ef5-b2b0-1afe4eee18e9
-- title:
--   Sensitivity separation: RecordSetLookup (complete source module)
-- statement:
--   Complete Lean source module `RecordSetLookup` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecordSetLookup.lean; original SHA-256 8dce1a34ad70d9182b78e5469447addfc950e195435007566d76b111b592f4bc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- A finite exact-row search tree. Search soundness does not assume that
   the tree is ordered: a successful search always matches an actual leaf. -/
import Definitions.Def_BS2_b3ba934b_Q2Enumeration

set_option autoImplicit false

namespace ThreeBoundRecordLookup

inductive Tree where
  | leaf : List ℕ → Tree
  | branch : List ℕ → Tree → Tree → Tree

def lexLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _::_ => true
  | _::_, [] => false
  | a::as, b::bs => if a=b then lexLess as bs else a<b

def Tree.elements : Tree → List (List ℕ)
  | .leaf row => [row]
  | .branch _ left right => left.elements ++ right.elements

def Tree.contains (row : List ℕ) : Tree → Bool
  | .leaf entry => decide (row=entry)
  | .branch pivot left right =>
      if lexLess row pivot then left.contains row else right.contains row

theorem Tree.contains_sound (tree : Tree) (row : List ℕ)
    (h : tree.contains row=true) : row∈tree.elements := by
  induction tree with
  | leaf entry =>
      have he : row=entry := of_decide_eq_true h
      simp [he,Tree.elements]
  | branch pivot left right hl hr =>
      simp only [Tree.contains] at h
      split at h
      · exact List.mem_append_left _ (hl h)
      · exact List.mem_append_right _ (hr h)

/-- Structurally recursive insertion sort gives a kernel-reducible version
    of the exact record; the standard merge-sort equality proves the match. -/
def recordFast (c : List ThreeBoundQ2.Kind × List Bool) : List ℕ := Id.run do
  let ts := c.1
  let vs := List.finRange ts.length
  let es := ThreeBoundQ2.edges ts.length
  let dirs := ThreeBoundQ2.directedEdges es c.2
  let residual := fun v : Fin ts.length =>
    ThreeBoundQ2.budget (ts.get v) - ThreeBoundQ2.outCount es c.2 v
  let incoming := fun v : Fin ts.length =>
    (dirs.filter fun e => ThreeBoundQ2.isGuard (ts.get e.1) && decide (e.2 = v)).length
  let typeCounts := (List.finRange 8).map fun t => (ts.filter fun u => u = t).length
  let external := ((vs.filter fun v => ThreeBoundQ2.isGuard (ts.get v)).map residual).sum
  let histogram := (List.finRange 8).flatMap fun t => [1,2].map fun h =>
    (vs.filter fun v => ts.get v = t ∧ min 2 (incoming v) = h).length
  let residuals := (vs.map residual).insertionSort (· ≤ ·)
  let prefixes := [1,2,3,4].map fun k =>
    if k ≤ ts.length then (residuals.take k).sum else 1000000
  return typeCounts ++ [external] ++ histogram ++ prefixes

theorem recordFast_eq (c : List ThreeBoundQ2.Kind × List Bool) :
    recordFast c = ThreeBoundQ2.record c := by
  simp only [recordFast,ThreeBoundQ2.record,List.mergeSort_eq_insertionSort]

def checkTypes (tree : Tree) (ts : List ThreeBoundQ2.Kind) : Bool :=
  (ThreeBoundQ2.casesFor ts).all fun c => tree.contains (recordFast c)

def checkLength (tree : Tree) (n : ℕ) : Bool :=
  (ThreeBoundQ2.typeLists 0 n).all (checkTypes tree)

def checkChunk (tree : Tree) (n start count : ℕ) : Bool :=
  (((ThreeBoundQ2.typeLists 0 n).drop start).take count).all (checkTypes tree)

theorem checkTypes_sound (tree : Tree) (ts : List ThreeBoundQ2.Kind)
    (h : checkTypes tree ts=true) (c : List ThreeBoundQ2.Kind × List Bool)
    (hc : c∈ThreeBoundQ2.casesFor ts) : ThreeBoundQ2.record c∈tree.elements :=
  by
    rw [← recordFast_eq]
    exact tree.contains_sound _ (List.all_eq_true.mp h c hc)

theorem checkLength_sound (tree : Tree) (n : ℕ)
    (h : checkLength tree n=true) (ts : List ThreeBoundQ2.Kind)
    (hts : ts∈ThreeBoundQ2.typeLists 0 n) (c : List ThreeBoundQ2.Kind × List Bool)
    (hc : c∈ThreeBoundQ2.casesFor ts) : ThreeBoundQ2.record c∈tree.elements :=
  checkTypes_sound tree ts (List.all_eq_true.mp h ts hts) c hc

theorem records_subset_of_checkLengths (tree : Tree)
    (h : ∀ n : Fin 8, checkLength tree n.val=true) :
    ∀ row∈ThreeBoundQ2.records, row∈tree.elements := by
  intro row hr
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
  obtain ⟨n,hn,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨ts,hts,hc⟩ := List.mem_flatMap.mp hc
  exact checkLength_sound tree n (h ⟨n,List.mem_range.mp hn⟩) ts hts c hc

end ThreeBoundRecordLookup

#print axioms ThreeBoundRecordLookup.records_subset_of_checkLengths


