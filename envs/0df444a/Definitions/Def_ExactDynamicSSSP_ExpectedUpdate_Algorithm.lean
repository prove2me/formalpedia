-- Prove2me | Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Algorithm
-- name    : ExactDynamicSSSP_ExpectedUpdate_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:27:18.104235+00:00
-- url     : https://prove2.me/theorems/9fe56d3d-9574-4718-b8a8-f183c2c95e76
-- title:
--   §§3.2–3.5, 5, App. A–B — the affected-region data structure, Algorithms 1 and 3, queries and initialization
-- statement:
--   This file defines the deterministic data structure and its instrumented execution.
--
--   **State.** The current graph (adjacency lists and the incoming records $Q_{x\to y}$ of the lists $C_y$, whose keys $d_x+w(x,y)$ are evaluated from the current tail label), explicit distance labels $d_v\in[0,\infty]$, certified parents, validity flags of the minimum pointers of the lists $C_v$, and the Fibonacci heap $C_{\rm main}$.
--
--   **Algorithm 1** (insertion or weight decrease of $u\to v$, Appendix A.1 conventions). Modify the record; if $v=s$ stop. Otherwise, if $d_u+w'<d_v$, set $d_v$ and the certified parent $u$, insert $v$ into $C_{\rm main}$, and repeatedly extract the minimum $x$ and relax every outgoing arc $x\to y$, $y\ne s$: on a strict improvement set $d_y$, record $x$ as parent, and insert or decrease $y$ in $C_{\rm main}$.
--
--   **Algorithm 3** (deletion or weight increase of $u\to v$). Test whether $u\to v$ is the old parent arc of $v$. If not, modify the record and stop. Otherwise save and mark $A=V(SPT_v)$ of the old tree, invalidate the minimum caches in $A$, apply the update, reset $d_y=\infty$ and the parent to null on $A$, scan every incoming arc $(x,y)$ with $y\in A$ and initialize $y$ from tails $x\notin A$, insert every finitely initialized vertex into $C_{\rm main}$, and run minimum-key relaxation inside $A$, publishing a settlement certificate and rebuilding the minimum pointer at each settlement; finally reattach parents and clear marks. Unreached vertices stay at $\infty$ with null parent.
--
--   **Dispatch.** Insertions and weight changes to a weight not larger than the old one run Algorithm 1; deletions and strict increases run Algorithm 3; an invalid request is ignored.
--
--   **Actual work and counts.** Each procedure returns its actual work (one unit per primitive pseudocode step — candidate evaluation, comparison, record/list access, label/parent write, mark, certificate — plus the actual work of every heap operation), the set $V'$ of processed vertices (the improved vertices for Algorithm 1, the whole old subtree $A$ for a tree update in Algorithm 3) and the set $E'$ of distinct scanned arcs (outgoing arcs of extracted vertices, and all incoming arcs of $A$).
--
--   **Initialization and queries.** Initialization runs Dijkstra from $s$ with the Fibonacci heap and then builds the records at additional work $m+n$. A state is *reachable* when it arises from initialization on some graph followed by any sequence of update requests. A distance query reads $d_v$ (work $1$); path reporting returns `none` at work $1$ when $d_v=\infty$ and otherwise follows certified parents back to $s$ and emits the vertex list $\pi=(s,\dots,v)$ at work $|\pi|$, the number of emitted vertices.
--
--   **Formalization Note** Because the labels and certified parents are stored explicitly, the preferred minimum record of a reachable vertex's list is the record of its certified parent arc, so the constant-time find-min, certificate and pointer-rebuild steps are charged as single units. The main loops carry a step budget of $n+1$ extractions, which suffices because each vertex is extracted at most once.
--
--   **Representation and cost convention.** Maps and lists specify the contents of indexed pointer structures extensionally. Known-handle erasure denotes pointer unlinking, list lengths denote cached degrees, and adjacency/subtree enumeration uses the stored incidence/child links. Charges count the corresponding source pointer operations in constant-size groups; processed/scanned sets are ghost observations. This cost is separate from evaluating Lean’s functional representation.
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), §3.2, PDF p.3; Algorithm 1, PDF p.4; §3.5, PDF p.5; §5, PDF p.7; Appendix A (A.1, A.2, Algorithm 3), PDF pp.14–15; Appendix B.1, PDF p.16 (printed = PDF pages)

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_FibHeap

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

noncomputable section

/-! # The affected-region data structure and its instrumented execution

Liang–Chen–Zhang, STOC 2027 submission #223: §3.2 (p. 3), Algorithm 1 (p. 4), §3.5 (p. 5),
§5 (p. 7), Appendix A (Algorithm 3, pp. 14–15) and Appendix B.1 (p. 16).

The state keeps the graph (adjacency lists and the per-arc incoming records `Q_{x→y}` of the
lists `C_y`, whose candidate keys `d_x + w(x,y)` are always evaluated from the current tail
label), explicit distance labels `d`, certified parents `par`, the validity flags of the
minimum pointers of the lists `C_y`, and the global Fibonacci heap `C_main`. Because the
labels and certified parents are explicit, the preferred minimum record of `C_y` of a
reachable vertex is the record of its certified parent arc; finding it, publishing a
settlement certificate and rebuilding a minimum pointer are constant-time steps and are
charged as such.

The maps and lists specify the contents of the source's indexed pointer structures. A map
update denotes a handle write; `outList`/`inList` denote adjacency enumeration, and the saved
subtree is enumerated through tree-child links. These expressions specify the resulting
contents, rather than charge for evaluating Lean's functional representation. The sets of
processed vertices and scanned arcs are ghost observations of the execution. Cached numerical
fields and redundant list links are projected away: the graph gives live candidate records,
and a certified parent identifies its preferred minimum handle. The work below charges the
corresponding source operations, including enumeration, marking, certificates and reattachment.

Every procedure returns the new state, its **actual work** (one unit per primitive step of the
pseudocode: arithmetic/comparison on a candidate key, list or record access, mark, label or
parent write, plus the actual work of every heap operation, see `FibHeap`), the set `V'` of
processed vertices and the set `E'` of distinct scanned arcs of §5. -/

/-- The data-structure state. -/
structure DS (n : ℕ) where
  /-- The current graph (adjacency lists and incoming records). -/
  graph : WDigraph n
  /-- The fixed source `s`. -/
  src : Fin n
  /-- Explicit distance labels `d_v ∈ [0, ∞]`. -/
  d : Fin n → ℝ≥0∞
  /-- Certified parents (`none` = null parent). -/
  par : Fin n → Option (Fin n)
  /-- Validity flags of the cached minimum pointers of the incoming lists `C_v`. -/
  valid : Fin n → Bool
  /-- The global propagation container `C_main`. -/
  heap : FibHeap n

/-- The outcome of one procedure: final state, actual work, processed vertices `V'`, and the
distinct scanned arcs `E'`. -/
structure Run (n : ℕ) where
  ds : DS n
  cost : ℕ
  processed : Finset (Fin n)
  scanned : Finset (Fin n × Fin n)

variable {n : ℕ}

/-- Relaxation of the scanned arc `x → y` (Algorithm 1 lines 15–25; Algorithm 3 lines 23–28):
the arc is recorded as scanned and its candidate `d_x + w(x,y)` is evaluated (work `1`); if
relaxing `y` is allowed and the candidate is strictly smaller than `d_y`, the record of
`(x, y)` is overwritten, `d_y` and the certified parent `par y := x` are set (work `1`), and
`y` is inserted into `C_main` or has its key decreased (the heap's actual work). Improved
vertices are added to the processed set. -/
def relaxArc (allowed : Bool) (x y : Fin n)
    (acc : DS n × ℕ × Finset (Fin n) × Finset (Fin n × Fin n)) :
    DS n × ℕ × Finset (Fin n) × Finset (Fin n × Fin n) :=
  let ds := acc.1
  let E := insert (x, y) acc.2.2.2
  let cand := ds.d x + ds.graph.ewt x y
  if allowed = true ∧ cand < ds.d y then
    let hc := if ds.heap.present y then ds.heap.decreaseKey y cand else ds.heap.insert y cand
    ({ ds with d := Function.update ds.d y cand, par := Function.update ds.par y (some x),
               heap := hc.1 },
     acc.2.1 + 2 + hc.2, insert y acc.2.2.1, E)
  else (ds, acc.2.1 + 1, acc.2.2.1, E)

/-- Minimum-key relaxation (Algorithm 1 lines 13–27 when `inc = false`; Algorithm 3 lines
19–30 when `inc = true`, restricted to the marked set `A`). Repeatedly `delete-min` from
`C_main`, settle the extracted vertex `x`, and scan all its outgoing arcs. In the decreasing
procedure every target except the source may be relaxed; in the increasing procedure only
unsettled targets in `A`, and each settlement also publishes the final-distance and
parent-record certificate of `x` and rebuilds the minimum pointer of `C_x` (work `2`, the
pointer becomes valid). The loop stops when the heap is empty (fuel `n + 1` suffices: each
vertex is extracted at most once). -/
def relaxLoop (inc : Bool) (A : Finset (Fin n)) :
    ℕ → DS n → Finset (Fin n) → ℕ → Finset (Fin n) → Finset (Fin n × Fin n) → Run n
  | 0, ds, _, c, P, E => ⟨ds, c, P, E⟩
  | fuel + 1, ds, S, c, P, E =>
    let r := ds.heap.deleteMin
    match r.2.1 with
    | none => ⟨{ ds with heap := r.1 }, c + r.2.2, P, E⟩
    | some x =>
      let S' := insert x S
      let ds1 : DS n :=
        { ds with heap := r.1,
                  valid := if inc then Function.update ds.valid x true else ds.valid }
      let cert := if inc then 2 else 0
      let acc := (ds1.graph.outList x).foldl
        (fun acc y => relaxArc
          (if inc then decide (y ∈ A ∧ y ∉ S') else decide (y ≠ ds.src)) x y acc)
        (ds1, 0, P, E)
      relaxLoop inc A fuel acc.1 S' (c + r.2.2 + cert + acc.2.1) acc.2.2.1 acc.2.2.2

/-- **Algorithm 1** with the conventions of Appendix A.1 — insertion of the arc `u → v` with
weight `w'` (`isInsert = true`) or a weight decrease to `w'`. Modify the record (work `1`, plus
`1` for the adjacency-list insertion). If `v` is the source only the record changes. Otherwise
compare the new candidate `d_u + w'` with `d_v` (work `1`); on strict improvement set `d_v`
and `par v := u` (work `1`), insert `v` into `C_main`, and run minimum-key relaxation. -/
def decUpdate (ds : DS n) (u v : Fin n) (w' : ℝ≥0) (isInsert : Bool) : Run n :=
  let G' := ds.graph.setArc u v (some w')
  let c0 := if isInsert then 2 else 1
  let ds0 : DS n := { ds with graph := G' }
  if v = ds.src then ⟨ds0, c0, ∅, ∅⟩
  else
    let cand := ds.d u + (w' : ℝ≥0∞)
    if cand < ds.d v then
      let hi := ds0.heap.insert v cand
      let ds1 : DS n := { ds0 with d := Function.update ds.d v cand,
                                   par := Function.update ds.par v (some u), heap := hi.1 }
      relaxLoop false ∅ (n + 1) ds1 ∅ (c0 + 2 + hi.2) {v} ∅
    else ⟨ds0, c0 + 1, ∅, ∅⟩

/-- Boundary scan step of Algorithm 3 (lines 13–17) at the scanned incoming arc `x → y` of a
marked vertex `y ∈ A`: work `1` to scan the record and test whether `x ∉ A`; if the tail is
outside `A` and `d_x + w(x,y) < d_y`, set `d_y` and `par y := x` (work `1`). -/
def boundaryScan (A : Finset (Fin n)) (y : Fin n) (acc : DS n × ℕ × Finset (Fin n × Fin n))
    (x : Fin n) : DS n × ℕ × Finset (Fin n × Fin n) :=
  let ds := acc.1
  let E := insert (x, y) acc.2.2
  let cand := ds.d x + ds.graph.ewt x y
  if x ∉ A ∧ cand < ds.d y then
    ({ ds with d := Function.update ds.d y cand, par := Function.update ds.par y (some x) },
     acc.2.1 + 2, E)
  else (ds, acc.2.1 + 1, E)

/-- **Algorithm 3** (Appendix A.2, pp. 14–15) — deletion of the present arc `u → v`
(`o' = none`) or an increase of its weight to `w'` (`o' = some w'`).

1. Test whether `u → v` is the old parent arc of `v` (work `1`).
2. If so, save `A = V(SPT_v)` of the old tree and mark its vertices (work `|A|`, enumeration
   through the tree-child links), and invalidate and suspend the minimum caches of `C_y`,
   `y ∈ A` (work `|A|`).
3. Apply the update to the adjacency lists and the record (work `1`, plus `1` for a deletion).
4. If the arc was not a parent arc, return.
5. Reset `d_y := ∞`, `par y := null` for `y ∈ A` (work `|A|`).
6. Scan every incoming arc `(x, y)` with `y ∈ A`; initialize `y` from tails `x ∉ A`
   (`boundaryScan`).
7. Insert every finitely initialized `y ∈ A` into `C_main` (work `1` per `y ∈ A` plus the
   heap's work).
8. Minimum-key relaxation inside `A` with settlement certificates (`relaxLoop true A`).
9. Reattach the repaired parent arcs, clear the marks and resume minimum queries (work `|A|`);
   unreached vertices keep `d = ∞`, a null parent and an invalid pointer, restored on demand.

The processed set is the whole old candidate subtree `A`; the scanned arcs are all incoming
arcs of `A` and all outgoing arcs of settled vertices. -/
def incUpdate (ds : DS n) (u v : Fin n) (o' : Option ℝ≥0) : Run n :=
  let G' := ds.graph.setArc u v o'
  let cUpd := if o'.isNone then 2 else 1
  if ds.par v ≠ some u then ⟨{ ds with graph := G' }, 1 + cUpd, ∅, ∅⟩
  else
    let A := subtree ds.src ds.par v
    let Al := (List.finRange n).filter fun y => decide (y ∈ A)
    let c1 := 1 + A.card + A.card + cUpd + A.card
    let ds1 : DS n :=
      { ds with graph := G',
                d := fun y => if y ∈ A then ⊤ else ds.d y,
                par := fun y => if y ∈ A then none else ds.par y,
                valid := fun y => if y ∈ A then false else ds.valid y }
    let bnd := Al.foldl (fun acc y => (G'.inList y).foldl (boundaryScan A y) acc) (ds1, 0, ∅)
    let ins := Al.foldl
      (fun (acc : FibHeap n × ℕ) y =>
        if bnd.1.d y < ⊤ then
          let r := acc.1.insert y (bnd.1.d y)
          (r.1, acc.2 + 1 + r.2)
        else (acc.1, acc.2 + 1))
      (bnd.1.heap, 0)
    let r := relaxLoop true A (n + 1) { bnd.1 with heap := ins.1 } ∅ (c1 + bnd.2.1 + ins.2) ∅
      bnd.2.2
    ⟨r.ds, r.cost + A.card, A, r.scanned⟩

/-- A single-arc update request: insert the absent arc `u → v` with weight `w`, delete the
present arc `u → v`, or change the weight of the present arc `u → v` to `w`. -/
inductive Update (n : ℕ)
  | insert (u v : Fin n) (w : ℝ≥0)
  | delete (u v : Fin n)
  | reweight (u v : Fin n) (w : ℝ≥0)

/-- Whether an update request is valid for the current graph. -/
def Update.Valid (G : WDigraph n) : Update n → Prop
  | .insert u v _ => u ≠ v ∧ G.wt u v = none
  | .delete u v => (G.wt u v).isSome
  | .reweight u v _ => (G.wt u v).isSome

/-- The arc `(u, v)` that an update request concerns. -/
def Update.arc : Update n → Fin n × Fin n
  | .insert u v _ => (u, v)
  | .delete u v => (u, v)
  | .reweight u v _ => (u, v)

/-- A **distance-decreasing** request (§3.1): insertion of an absent arc (no loop), or a strict
weight decrease of a present arc. -/
def Update.IsDecreasing (G : WDigraph n) : Update n → Prop
  | .insert u v _ => u ≠ v ∧ G.wt u v = none
  | .delete _ _ => False
  | .reweight u v w => ∃ w₀, G.wt u v = some w₀ ∧ w < w₀

/-- A **distance-increasing** request (§3.1): deletion of a present arc, or a strict weight
increase of a present arc. -/
def Update.IsIncreasing (G : WDigraph n) : Update n → Prop
  | .insert _ _ _ => False
  | .delete u v => (G.wt u v).isSome
  | .reweight u v w => ∃ w₀, G.wt u v = some w₀ ∧ w₀ < w

/-- The graph after a valid update. -/
def Update.applyTo (G : WDigraph n) : Update n → WDigraph n
  | .insert u v w => G.setArc u v (some w)
  | .delete u v => G.setArc u v none
  | .reweight u v w => G.setArc u v (some w)

/-- Dispatch one update (§3.3–3.4): insertions and weight changes to a weight `≤` the old one
run Algorithm 1 (`decUpdate`); deletions and strict weight increases run Algorithm 3
(`incUpdate`). An invalid request is ignored at work `1`. -/
def applyUpdate (ds : DS n) : Update n → Run n
  | .insert u v w =>
    if u ≠ v ∧ ds.graph.wt u v = none then decUpdate ds u v w true else ⟨ds, 1, ∅, ∅⟩
  | .delete u v => if (ds.graph.wt u v).isSome then incUpdate ds u v none else ⟨ds, 1, ∅, ∅⟩
  | .reweight u v w =>
    match ds.graph.wt u v with
    | none => ⟨ds, 1, ∅, ∅⟩
    | some w0 => if w ≤ w0 then decUpdate ds u v w false else incUpdate ds u v (some w)

/-- **Initialization** (§3.2, p. 3; Appendix A, p. 14): static Dijkstra from `s` with the
Fibonacci heap (the minimum-key relaxation from `d_s = 0`), followed by the construction of all
incoming records `Q_{x→y}` in additional work `m + n`. -/
def initDS (G : WDigraph n) (s : Fin n) : Run n :=
  let hi := (FibHeap.empty : FibHeap n).insert s 0
  let ds0 : DS n :=
    ⟨G, s, Function.update (fun _ => ⊤) s 0, fun _ => none, fun _ => true, hi.1⟩
  let r := relaxLoop false ∅ (n + 1) ds0 ∅ hi.2 {s} ∅
  ⟨r.ds, r.cost + G.numArcs + n, r.processed, r.scanned⟩

/-- Run a sequence of update requests. -/
def runUpdates (ds : DS n) : List (Update n) → DS n
  | [] => ds
  | u :: us => runUpdates (applyUpdate ds u).ds us

/-- `ds` is a state of the data structure for the graph `G` and source `s`: it is obtained by
initializing on some graph `G₀` with source `s` and applying some sequence of update requests,
and its current graph is `G`. Arc weights are arbitrary nonnegative reals (zero weights and
ties included). -/
def IsReachableState (G : WDigraph n) (s : Fin n) (ds : DS n) : Prop :=
  ∃ (G₀ : WDigraph n) (us : List (Update n)), ds = runUpdates (initDS G₀ s).ds us ∧ ds.graph = G

/-- The certified shortest-path tree computed by the initialization (Dijkstra) on `G`. -/
def spt (G : WDigraph n) (s : Fin n) : Fin n → Option (Fin n) := (initDS G s).ds.par

/-! ## Queries (§3.5, p. 5) -/

/-- Distance query: read the explicit label `d_v` (work `1`). -/
def distQuery (ds : DS n) (v : Fin n) : ℝ≥0∞ × ℕ := (ds.d v, 1)

/-- The certified parent chain from `x` back towards the source (at most `fuel` steps). -/
def parentChain (par : Fin n → Option (Fin n)) (s : Fin n) : ℕ → Fin n → List (Fin n)
  | 0, x => [x]
  | k + 1, x =>
    if x = s then [x]
    else match par x with
      | none => [x]
      | some y => x :: parentChain par s k y

/-- Path reporting: if `d_v = ∞` report unreachability (work `1`); otherwise follow certified
parents from `v` back to `s` and emit the path `π = (s, …, v)` as its vertex list, at work
`|π|` = the number of emitted vertices. -/
def pathReport (ds : DS n) (v : Fin n) : Option (List (Fin n)) × ℕ :=
  if ds.d v = ⊤ then (none, 1)
  else
    let l := (parentChain ds.par ds.src n v).reverse
    (some l, l.length)

end

end ExactDynamicSSSP.ExpectedUpdate


