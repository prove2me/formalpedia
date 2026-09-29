-- Prove2me | Definitions.Def_NagamochiIbaraki_EdgeConn_Forest
-- name    : NagamochiIbaraki_EdgeConn_Forest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:01:14.955171+00:00
-- url     : https://prove2.me/theorems/71ffb1d1-7171-4d8b-9011-29e30498792b
-- title:
--   Procedure FOREST as a nondeterministic transition system: states, select/scan/finish steps, runs and the classes E_i
-- statement:
--   Procedure FOREST (Nagamochi–Ibaraki 1992, lines 1–11) partitions the edge set of a multigraph $G = (V, E)$ into classes $E_1, E_2, \dots, E_{|E|}$ by a single graph search. It keeps a label $r(v) \in \mathbb{N}$ for every node, initially $0$, and marks nodes and edges "scanned". While some node is unscanned, it chooses an unscanned node $x$ with the largest label $r$ (line 5); then, for each unscanned edge $e$ joining $x$ to another node $y$ (line 6), it
--
--   1. puts $e$ into $E_{r(y)+1}$ (line 7),
--   2. increases $r(x)$ by one if $r(x) = r(y)$ (line 8),
--   3. increases $r(y)$ by one (line 9),
--   4. marks $e$ scanned (line 10);
--
--   finally it marks $x$ scanned (line 11). Lines 7 and 8 use the value of $r(y)$ before line 9 changes it.
--
--   A **state** records the labels $r$, for every edge the index $i$ of its class ($0$ while the edge is unscanned), the set of scanned nodes, the node $x$ currently being processed (if any), and the order in which nodes were chosen. A **step** is one of three moves:
--
--   - **select** (line 5): no node is in progress; an unscanned node $x$ whose label is maximal among the unscanned nodes becomes the current node;
--   - **scan** (lines 6–10): an unscanned edge $e$ between the current node $x$ and a node $y$ is put into $E_{r(y)+1}$ and the labels are updated as above;
--   - **finish** (line 11): the current node has no unscanned incident edge left and is marked scanned.
--
--   Ties in line 5 and the order of edges in line 6 are left open: every choice is a legal step, so the theorems of the mission hold for every execution. A **run** of length $K$ is a sequence of states $\sigma_0, \sigma_1, \dots, \sigma_K$ with $\sigma_0$ the initial state (all labels $0$, nothing scanned, all classes empty) and a step from each $\sigma_k$ to $\sigma_{k+1}$. It is **completed** when every node is scanned at time $K$, so that the test of line 4 fails. The class $E_i$ **at time** $k$ is the set of edges whose index in $\sigma_k$ equals $i$, and $E_1 \cup \dots \cup E_i$ at time $k$ is the set of edges whose index lies between $1$ and $i$ (the edge set of $G_i$).
--
--   **Formalization Note** The step relation is a `Prop`, not a function, precisely so that no tie-breaking rule is imposed. The running-time analysis of FOREST (buckets, O(|V| + |E|)) is not formalized.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), pp. 584–585, Procedure FOREST (lines 1–11)

import Mathlib

namespace NagamochiIbaraki.EdgeConn

/-! Procedure FOREST (Nagamochi–Ibaraki 1992, pp. 584–585, lines 1–11), as a nondeterministic
transition system. Line 5 ("an unscanned node with the largest r") and line 6 ("for each
unscanned edge incident to x") leave choices open; every choice is a legal step. -/

variable {V E : Type*}

/-- A state of FOREST.
* `r v` is the label `r(v)`;
* `idx e` is the class of the edge `e`: `0` while `e` is unscanned, and `i ≥ 1` once `e ∈ E_i`;
* `done` is the set of nodes marked "scanned" (line 11);
* `cur = some x` while the for-loop of line 6 runs for the node `x` chosen at line 5;
* `order` lists the nodes in the order line 5 chose them. -/
structure State (V E : Type*) where
  r : V → ℕ
  idx : E → ℕ
  done : Finset V
  cur : Option V
  order : List V

/-- The initial state (lines 1–3): all classes empty, every node and edge unscanned, `r ≡ 0`. -/
def init : State V E where
  r := fun _ => 0
  idx := fun _ => 0
  done := ∅
  cur := none
  order := []

/-- One step of FOREST.
* **select** (line 5): no node is being processed, and `x` is an unscanned node whose label is
  largest among the unscanned nodes; `x` becomes the current node.
* **scan** (lines 6–10): `e` is an unscanned edge joining the current node `x` to `y`. Line 7
  puts `e` into `E_{r(y)+1}`; line 8 increments `r(x)` if `r(x) = r(y)`; line 9 increments
  `r(y)`; line 10 marks `e` scanned (its class becomes nonzero). Lines 7 and 8 use the value of
  `r(y)` before line 9.
* **finish** (line 11): the current node `x` has no unscanned incident edge left; `x` is marked
  scanned. -/
def Step [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (s t : State V E) : Prop :=
  (∃ x : V, s.cur = none ∧ x ∉ s.done ∧ (∀ v, v ∉ s.done → s.r v ≤ s.r x) ∧
      t = { s with cur := some x, order := s.order ++ [x] }) ∨
  (∃ (x y : V) (e : E), s.cur = some x ∧ s.idx e = 0 ∧ ends e = s(x, y) ∧
      t = { s with
              idx := Function.update s.idx e (s.r y + 1),
              r := Function.update
                (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
                y (s.r y + 1) }) ∨
  (∃ x : V, s.cur = some x ∧ (∀ e : E, x ∈ ends e → s.idx e ≠ 0) ∧
      t = { s with done := insert x s.done, cur := none })

/-- `σ 0, σ 1, …, σ K` is an execution of FOREST of length `K` from the initial state. -/
def IsRun [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (σ : ℕ → State V E) (K : ℕ) :
    Prop :=
  σ 0 = init ∧ ∀ k, k < K → Step ends (σ k) (σ (k + 1))

/-- A completed execution: at time `K` every node is scanned, so the while-test of line 4 fails
and FOREST terminates. -/
def IsCompletedRun [Fintype V] [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (σ : ℕ → State V E) (K : ℕ) : Prop :=
  IsRun ends σ K ∧ (σ K).done = Finset.univ

/-- The class `E_i` held by the state `s` (the set `E_i` "at that time instant"). -/
def cls [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => s.idx e = i)

/-- The edge set `E_1 ∪ E_2 ∪ ⋯ ∪ E_i` of `G_i` held by the state `s`
(empty for `i = 0`). -/
def upto [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => 1 ≤ s.idx e ∧ s.idx e ≤ i)

end NagamochiIbaraki.EdgeConn


