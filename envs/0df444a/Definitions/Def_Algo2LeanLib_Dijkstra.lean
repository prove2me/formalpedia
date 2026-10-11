-- Prove2me | Definitions.Def_Algo2LeanLib_Dijkstra
-- name    : Algo2LeanLib_Dijkstra
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:38:57.482312+00:00
-- url     : https://prove2.me/theorems/8ee6870a-4b12-4819-9feb-36b82975f579
-- title:
--   Algo2LeanLib.Dijkstra definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.Dijkstra`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Dijkstra.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable shortest-path mathematics for Dijkstra implementations.

This module imports neither a compiled algorithm nor the Algo2Lean runtime.
Distance sequences are ordinary functions `Int → Int`. A queue backend only
needs to supply minimum selection, the relaxation scan, and exhaustion; the
path, frontier, and shortest-distance proofs are shared across backends.
-/

namespace Algo2Lean.Dijkstra

/-- `edge u v weight` describes a directed edge; parallel edges are allowed. -/
abbrev Edges := Int → Int → Int → Prop

/-- A finite walk from `source`, recording its endpoint and total edge weight.
    Repeated vertices are allowed, so shortestness compares all finite walks. -/
inductive Path (edge : Edges) (source : Int) : Int → Int → Prop where
  | empty : Path edge source source 0
  | extend {vertex next cost weight : Int} :
      Path edge source vertex cost → edge vertex next weight →
      Path edge source next (cost + weight)

def NonnegativeEdges (edge : Edges) : Prop :=
  ∀ u v weight, edge u v weight → 0 ≤ weight



/-- Every settled distance is a lower bound for every route to that vertex.
    With route witnesses, this says that settled distances are already exact. -/
def SettledOptimal (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop :=
  ∀ vertex, settled vertex → ∀ cost, Path edge source vertex cost → distance vertex ≤ cost

/-- All edges out of settled vertices have been relaxed. In particular, every
    edge crossing into the unsettled region gives that vertex a finite bound. -/
def FrontierBound (edge : Edges) (distance : Int → Int) (settled : Int → Prop) : Prop :=
  ∀ u v weight, settled u → ¬ settled v → edge u v weight →
    0 ≤ distance v ∧ distance v ≤ distance u + weight

/-- Every finite tentative distance comes from an actual route. -/
def DistanceWitnesses (edge : Edges) (source : Int) (distance : Int → Int) : Prop :=
  ∀ vertex, 0 ≤ distance vertex → Path edge source vertex (distance vertex)

def IsShortest (edge : Edges) (source vertex cost : Int) : Prop :=
  Path edge source vertex cost ∧
    ∀ otherCost, Path edge source vertex otherCost → cost ≤ otherCost













abbrev Adjacency := Int → List (Int × Int)

/-- The mathematical graph used by the path lemmas, extracted from adjacency
    lists on the valid finite vertex range. -/
def representedEdges (size : Int) (adjacency : Adjacency) : Edges :=
  fun source target weight => 0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source

/-- The finite vertex range is used only by proofs, not by the source program. -/
def vertexRange (size : Int) : List Int := (List.range size.toNat).map Int.ofNat

@[simp] theorem vertexRange_length (size : Int) : (vertexRange size).length = size.toNat := by
  simp [vertexRange]



@[simp] theorem vertexRange_member (size vertex : Int) :
    vertex ∈ vertexRange size ↔ 0 ≤ vertex ∧ vertex < size := by
  simp only [vertexRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, bound, rfl⟩
    change 0 ≤ (index : Int) ∧ (index : Int) < size
    omega
  · rintro ⟨nonnegative, bound⟩
    exact ⟨vertex.toNat, by omega, Int.toNat_of_nonneg nonnegative⟩









/-- Number of adjacency entries still eligible to be visited. Parallel edges
    and shared linked suffixes are counted once for each source-list occurrence. -/
def edgeBudget (adjacency : Adjacency) (remaining : List Int) : Nat :=
  (remaining.map (fun vertex => (adjacency vertex).length)).sum















/-! Pure invariants for every iteration of Dijkstra, independent of the queue
implementation, storage layout, and compiler-generated transition system. -/

def updateDistance (distance : Int → Int) (target value : Int) : Int → Int :=
  fun vertex => if vertex = target then value else distance vertex

def relaxDistance (distance : Int → Int) (target candidate : Int) : Int → Int :=
  if distance target < 0 ∨ candidate < distance target then updateDistance distance target candidate else distance

@[simp] theorem update_distance_same (distance : Int → Int) (target value : Int) :
    updateDistance distance target value target = value := by simp [updateDistance]

@[simp] theorem update_distance_other (distance : Int → Int) (target value vertex : Int)
    (different : vertex ≠ target) : updateDistance distance target value vertex = distance vertex := by
  simp [updateDistance, different]









structure DistanceInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop where
  sourceZero : ¬ settled source → distance source = 0
  witnesses : DistanceWitnesses edge source distance
  settledOptimal : SettledOptimal edge source distance settled
  settledFinite : ∀ vertex, settled vertex → 0 ≤ distance vertex
  unknown : ∀ vertex, distance vertex < 0 → distance vertex = -1

structure SearchInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop extends DistanceInvariant edge source distance settled where
  frontier : FrontierBound edge distance settled

/-- During one adjacency scan the selected vertex has just been settled.
    All older settled vertices retain their complete frontier bounds, while
    `processed` records the selected vertex's edges already handled. -/
structure RelaxationInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) (selected : Int) (processed : List (Int × Int))
    : Prop extends DistanceInvariant edge source distance settled where
  selectedSettled : settled selected
  oldFrontier : ∀ u v weight, settled u → u ≠ selected → ¬ settled v → edge u v weight →
    0 ≤ distance v ∧ distance v ≤ distance u + weight
  processedFrontier : ∀ v weight, (v, weight) ∈ processed → ¬ settled v →
    0 ≤ distance v ∧ distance v ≤ distance selected + weight

def settleVertex (settled : Int → Prop) (selected : Int) : Int → Prop :=
  fun vertex => settled vertex ∨ vertex = selected











def initialDistances (source : Int) : Int → Int := fun vertex => if vertex = source then 0 else -1









/-- Pure description of a complete adjacency scan. The execution proof supplies
    its settled/unsettled branches; comparison and update are `relaxDistance`. -/
inductive RelaxScan (settled : Int → Prop) (selected : Int) :
    List (Int × Int) → (Int → Int) → (Int → Int) → Prop where
  | empty (distance : Int → Int) : RelaxScan settled selected [] distance distance
  | skip {target weight : Int} {rest : List (Int × Int)}
      {distance result : Int → Int} : settled target →
      RelaxScan settled selected rest distance result →
      RelaxScan settled selected ((target, weight) :: rest) distance result
  | relax {target weight : Int} {rest : List (Int × Int)}
      {distance result : Int → Int} : ¬ settled target →
      RelaxScan settled selected rest
        (relaxDistance distance target (distance selected + weight)) result →
      RelaxScan settled selected ((target, weight) :: rest) distance result









/-- Each result entry is either the unreachable sentinel `-1` or the exact
    weight of a shortest path. Callers need no heap or transcript in this predicate. -/
def ShortestDistances (edge : Edges) (source : Int) (distance : Int → Int) : Prop :=
  ∀ vertex,
    (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
    (distance vertex ≠ -1 → IsShortest edge source vertex (distance vertex))









/-! Backend-independent queue and complete-loop contracts. -/



/-- The selected vertex is unsettled and has a minimum finite tentative distance. -/
structure MinimumSelection (distance : Int → Int) (settled : Int → Prop)
    (selected : Int) : Prop where
  unsettled : ¬ settled selected
  finite : 0 ≤ distance selected
  minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
    distance selected ≤ distance vertex

def Exhausted (distance : Int → Int) (settled : Int → Prop) : Prop :=
  ∀ vertex, ¬ settled vertex → distance vertex < 0









/-- A finite logical account of the outer loop, independent of its queue,
    heap, compiler, and transition labels. The list records selected vertices;
    each selection scans its entire adjacency list, then the queue is exhausted.
    A compiled execution must establish this relation before using its theorems. -/
inductive SearchRun (edge : Edges) (adjacency : Adjacency) :
    (Int → Int) → (Int → Prop) → (Int → Int) → List Int → Prop where
  | done (distance : Int → Int) (settled : Int → Prop)
      (exhausted : Exhausted distance settled) :
      SearchRun edge adjacency distance settled distance []
  | select {distance next output : Int → Int} {settled : Int → Prop}
      {selected : Int} {vertices : List Int}
      (minimum : MinimumSelection distance settled selected)
      (represents : ∀ target weight,
        (target, weight) ∈ adjacency selected ↔ edge selected target weight)
      (scan : RelaxScan (settleVertex settled selected) selected
        (adjacency selected) distance next)
      (rest : SearchRun edge adjacency next (settleVertex settled selected) output vertices) :
      SearchRun edge adjacency distance settled output (selected :: vertices)











end Algo2Lean.Dijkstra


