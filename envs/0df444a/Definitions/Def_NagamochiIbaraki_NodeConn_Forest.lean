-- Prove2me | Definitions.Def_NagamochiIbaraki_NodeConn_Forest
-- name    : NagamochiIbaraki_NodeConn_Forest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:07:47.485983+00:00
-- url     : https://prove2.me/theorems/ea27e078-c035-48cc-9ba0-bee09064beea
-- title:
--   Procedure FOREST as a nondeterministic transition system: states, select / scan / finish steps, runs and the classes E*_i
-- statement:
--   Procedure FOREST (lines 1–11 of the paper) scans the nodes of a graph $G = (V, E)$ one at a time and distributes the edges into classes $E_1, E_2, \dots, E_{|E|}$. Its state consists of
--
--   1. a label $r(v) \in \mathbb N$ for each node $v$;
--   2. for each edge $e$, its class: $0$ while $e$ is unscanned, and $i \ge 1$ once $e \in E_i$;
--   3. the set of nodes already marked "scanned";
--   4. the node $x$ currently being processed, if any;
--   5. the list of nodes in the order in which they were chosen.
--
--   Initially (lines 1–3) all labels are $0$, all classes are empty and nothing is scanned. A **step** is one of:
--
--   - **select** (line 5): no node is being processed, and an unscanned node $x$ whose label is largest among the unscanned nodes becomes the current node;
--   - **scan** (lines 6–10): for an unscanned edge $e$ joining the current node $x$ to a node $y$, put $e$ into $E_{r(y)+1}$; if $r(x) = r(y)$ then increase $r(x)$ by one; increase $r(y)$ by one (lines 7 and 8 use the value of $r(y)$ before line 9);
--   - **finish** (line 11): the current node has no unscanned incident edge left, and it is marked scanned.
--
--   Ties at line 5 and the order of the edges at line 6 are left open: every choice is a legal step. A **run** of length $K$ is a sequence of states $\sigma_0, \sigma_1, \dots, \sigma_K$ with $\sigma_0$ initial and each $\sigma_{k+1}$ obtained from $\sigma_k$ by one step; it is **completed** when every node is scanned in $\sigma_K$, so that the while-test of line 4 fails. For a state $s$ the class $E^*_i$ is the set of edges of class $i$ in $s$ (the paper's "intermediate edge sets at a given time instant"), $E_1 \cup \dots \cup E_i$ is the set of edges of class between $1$ and $i$, and for the final state of a completed run these are the output classes $E_i$ and the edge set of $G_i$. Finally, "$u$ is scanned before $v$" means that $u$ precedes $v$ in the recorded selection order.
--
--   **Formalization Note** `State`, `init`, `Step`, `IsRun`, `IsCompletedRun`, `cls s i` ($E^*_i$ in $s$), `upto s i` ($E_1 \cup \dots \cup E_i$ in $s$) and `scanBefore s u v` (via `List.idxOf` on the selection order). A time instant of the paper is a state $\sigma_k$, $k \le K$, of a run.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), pp. 584–585, Procedure FOREST lines 1–11; p. 590, notation E_i and E*_i; p. 588, orientation paragraph (scan order)

import Mathlib

namespace NagamochiIbaraki.NodeConn

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

/-- The class `E_i` held by the state `s` (the set `E*_i` "at that time instant"). -/
def cls [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => s.idx e = i)

/-- The edge set `E_1 ∪ E_2 ∪ ⋯ ∪ E_i` of `G_i` held by the state `s`
(empty for `i = 0`). -/
def upto [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => 1 ≤ s.idx e ∧ s.idx e ≤ i)

/-- `scanBefore s u v`: in the selection order recorded by `s` (line 5), the node `u` was chosen
before the node `v`. Applied to the final state of a completed run, whose `order` lists every
node exactly once, this is "u is scanned before v". -/
def scanBefore [DecidableEq V] (s : State V E) (u v : V) : Prop :=
  s.order.idxOf u < s.order.idxOf v

end NagamochiIbaraki.NodeConn


