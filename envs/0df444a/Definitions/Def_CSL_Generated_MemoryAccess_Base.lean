-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Base
-- name    : CSL_Generated_MemoryAccess_Base
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:16:39.711553+00:00
-- url     : https://prove2.me/theorems/8d17c06e-4b90-40b7-99ee-06d829758b6e
-- title:
--   Coded sorting library: Generated / MemoryAccess / Base
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Base` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Base

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventProperties

namespace CSL.Construction.PhysicalFramePaths

/-- A finite lookup certificate. Branch pivots need no trusted ordering:
the checks below validate every reachable key and every actual port. -/
inductive VisitTree where
  | empty
  | leaf (key : Nat) (visits : List Nat)
  | branch (pivot : Nat) (left right : VisitTree)

namespace VisitTree

def hasKey : VisitTree → Nat → Bool
  | .empty, _ => false
  | .leaf k _, r => r == k
  | .branch p l h, r => if r < p then l.hasKey r else h.hasKey r

def lookup : VisitTree → Nat → List Nat
  | .empty, _ => []
  | .leaf k vs, r => if r == k then vs else []
  | .branch p l h, r => if r < p then l.lookup r else h.lookup r

def keys : VisitTree → List Nat
  | .empty => []
  | .leaf k _ => [k]
  | .branch _ l h => l.keys ++ h.keys

theorem mem_keys_of_hasKey (t : VisitTree) (r : Nat) (hr : t.hasKey r = true) :
    r ∈ t.keys := by
  induction t with
  | empty => simp [hasKey] at hr
  | leaf k vs => simpa [hasKey, keys] using hr
  | branch p l h il ih =>
    by_cases hp : r < p
    · exact List.mem_append_left _ (il (by simpa [hasKey, hp] using hr))
    · exact List.mem_append_right _ (ih (by simpa [hasKey, hp] using hr))

theorem lookup_eq_nil (t : VisitTree) (r : Nat) (hr : t.hasKey r = false) :
    t.lookup r = [] := by
  induction t with
  | empty => rfl
  | leaf k vs => simpa [lookup, hasKey] using congrArg (fun b => if b then vs else []) hr
  | branch p l h il ih =>
    by_cases hp : r < p
    · simpa [lookup, hp] using il (by simpa [hasKey, hp] using hr)
    · simpa [lookup, hp] using ih (by simpa [hasKey, hp] using hr)

end VisitTree

def visitsCovered (events : List FrameEvent) (t : VisitTree) : Bool :=
  events.all (fun e => e.ports.all t.hasKey)

def visitsChecked (events : List FrameEvent) (t : VisitTree) : Bool :=
  t.keys.all (fun r => eventVisits r events == t.lookup r)

/-- Ordinary kernel checks on the actual ports and the finite keys imply
equality for every natural register index, including absent indices. -/
theorem eventVisits_of_tree (events : List FrameEvent) (t : VisitTree)
    (covered : visitsCovered events t = true)
    (checked : visitsChecked events t = true) (r : Nat) :
    eventVisits r events = t.lookup r := by
  cases hr : t.hasKey r with
  | true =>
    have h := (List.all_eq_true.mp checked) r (t.mem_keys_of_hasKey r hr)
    simpa only [beq_iff_eq] using h
  | false =>
    rw [t.lookup_eq_nil r hr]
    apply eventVisits_eq_nil
    intro e he hmem
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp covered) e he)) r hmem
    simp [hr] at h

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_of_tree


