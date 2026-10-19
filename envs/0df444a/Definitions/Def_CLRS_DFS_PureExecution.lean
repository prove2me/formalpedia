-- Prove2me | Definitions.Def_CLRS_DFS_PureExecution
-- name    : CLRS_DFS_PureExecution
-- status  : Definition
-- author  : @fizzyinc3
-- created : 2026-10-17T03:55:10.522926+00:00
-- url     : https://prove2.me/theorems/e5a99556-f6e0-4739-ab32-3c531c797e1e
-- title:
--   Pure finite-state execution of ordered recursive DFS
-- statement:
--   This is the finite-state execution model of ordered recursive depth-first search from CLRS §20.3.
--
--   A state consists of six integer sequences (color, parent, discovery time, finish time, finish order and tree label) and counters for event time, finished vertices and completed trees. Initially the colors and times are zero, the other arrays have value $-1$, and the counters are zero. Entering a vertex increments time, records its discovery, marks it gray and assigns its tree label. Leaving a vertex marks it black, increments time, records its finish time and appends it to finish order.
--
--   Finite big-step derivations describe a vertex visit, an adjacency-list scan, and the outer root loop. Every adjacency occurrence is processed in its stored order. A white neighbor gets its parent assigned and is visited recursively; an already discovered neighbor is skipped. A white outer-loop vertex starts the next numbered tree. The natural-number cost counts the actual traversal's graph_work events: three per vertex visit, two per scanned occurrence or outer-loop iteration, and one extra per recursive tree edge or new root. The four fixed entry, allocation, loop-start and return events are excluded.
--
--   The completion predicate records all-black colors, event time $2n$, $n$ finished vertices, at most $n$ trees, and the existing local timestamp, parent, edge-scan, finish-order and label certificate. It contains no heap allocation or generated transition. This model is used to isolate the mathematical traversal invariant from the concrete implementation proof.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition, Section 20.3, DFS and DFS-VISIT, Theorems 20.7 and 20.9. Pure big-step transcription of the existing generated program in Definitions.Def_CLRS_DFS_Program on Prove2Me. Supporting source: Jessica Su, Stanford CS 161 Lecture 10, Sections 2.1–2.4, PDF pages 4–9, https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture10-draft.pdf .

import Definitions.Def_CLRS_DFS_LocalCertificate

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal

namespace CLRS.DFS.Pure

/-- The six arrays are color, parent, discovery, finish, finish order and tree label. -/
structure State where
  arrays : Fin 6 → Seq
  clock : Int
  finished : Int
  count : Int

def initial : State :=
  ⟨fun i => if i = 0 ∨ i = 2 ∨ i = 3 then fun _ => 0 else fun _ => -1, 0, 0, 0⟩

def write (s : State) (a : Fin 6) (i v : Int) : State :=
  { s with arrays := Function.update s.arrays a (Function.update (s.arrays a) i v) }

def enter (s : State) (u label : Int) : State :=
  let s := {s with clock := s.clock + 1}
  write (write (write s 2 u s.clock) 0 u 1) 5 u label

def leave (s : State) (u : Int) : State :=
  let s := write s 0 u 2
  let s := {s with clock := s.clock + 1}
  let s := write (write s 3 u s.clock) 4 s.finished u
  {s with finished := s.finished + 1}

def nextTree (s : State) : State := {s with count := s.count + 1}

inductive Task where
  | visit (u label : Int)
  | scan (u label : Int) (remaining : List Nat)
  | roots (remaining : List Int)

/-- Finite big-step derivations of ordinary recursive DFS. The final natural
number counts the graph_work events inside the traversal, excluding the four
entry/constructor/loop-start/return events. Every adjacency occurrence is scanned. -/
inductive Eval (g : Graph) : Task → State → State → Nat → Prop where
  | visit {u label a b k} : Vertex g u →
      Eval g (.scan u label (g.neighbors u.toNat)) (enter a u label) b k →
      Eval g (.visit u label) a (leave b u) (k + 3)
  | scan_nil (u label a) : Eval g (.scan u label []) a a 0
  | scan_seen {u label vs a b k} {v : Nat} : a.arrays 0 v ≠ 0 →
      Eval g (.scan u label vs) a b k →
      Eval g (.scan u label (v :: vs)) a b (k + 2)
  | scan_fresh {u label vs a b c j k} {v : Nat} : a.arrays 0 v = 0 →
      Eval g (.visit v label) (write a 1 v u) b j →
      Eval g (.scan u label vs) b c k →
      Eval g (.scan u label (v :: vs)) a c (j + k + 3)
  | roots_nil (a) : Eval g (.roots []) a a 0
  | roots_seen {u us a b k} : a.arrays 0 u ≠ 0 →
      Eval g (.roots us) a b k → Eval g (.roots (u :: us)) a b (k + 2)
  | roots_fresh {u us a b c j k} : a.arrays 0 u = 0 →
      Eval g (.visit u a.count) a b j → Eval g (.roots us) (nextTree b) c k →
      Eval g (.roots (u :: us)) a c (j + k + 3)

/-- Completed pure traversal, in the local invariant vocabulary used by the
existing DFS/SCC contracts. No heap or generated transition appears here. -/
def Completed (g : Graph) (input : Seq) (s : State) : Prop :=
  s.clock = 2 * (g.size : Int) ∧ s.finished = (g.size : Int) ∧
  (∀ v : Int, Vertex g v → s.arrays 0 v = 2) ∧
  ∃ count : Nat, s.count = (count : Int) ∧ count ≤ g.size ∧
    LocalCertificate g input (s.arrays 1) (s.arrays 2) (s.arrays 3)
      (s.arrays 4) (s.arrays 5) count

end CLRS.DFS.Pure


