-- Prove2me | Definitions.Def_Algo2LeanLib_DijkstraExecution
-- name    : Algo2LeanLib_DijkstraExecution
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:14.528863+00:00
-- url     : https://prove2.me/theorems/e801d857-042c-41b1-aa31-06b85b7f8435
-- title:
--   Algo2LeanLib.DijkstraExecution definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.DijkstraExecution`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/DijkstraExecution.lean

import Definitions.Def_Algo2LeanLib_Dijkstra

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The finite Dijkstra driver shared by compiled queue backends. It composes
verified local iterations; it does not assume a search transcript, shortest
path correctness, or termination of the whole algorithm.
-/

namespace Algo2Lean.Dijkstra.Execution

/-- Concrete states may include a heap, queue layout, and amortized potential.
    Accounting is an arbitrary compositional relation, rather than a fixed
    binary-heap cost formula. Completion is the compiled continuation contract. -/
structure Interface (State : Type) where
  distance : State → Int → Int
  settled : State → Int → Prop
  invariant : State → List Int → Prop
  completion : State → State → Prop
  accounting : State → State → Nat → Nat → Prop
  zero : ∀ state, accounting state state 0 0
  compose : ∀ {before middle after firstVertices firstEdges lastVertices lastEdges},
    accounting before middle firstVertices firstEdges →
    accounting middle after lastVertices lastEdges →
    accounting before after (firstVertices + lastVertices) (firstEdges + lastEdges)
  weaken : ∀ {before after vertices edges moreVertices moreEdges},
    accounting before after vertices edges → vertices ≤ moreVertices → edges ≤ moreEdges →
    accounting before after moreVertices moreEdges

/-- One verified extraction and adjacency scan. The premises describe local
    state changes and one compiled segment; all recursive reasoning is shared. -/
structure Iteration {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (before after : State) (remaining : List Int) (selected : Int) : Prop where
  member : selected ∈ remaining
  next : api.invariant after (remaining.erase selected)
  minimum : MinimumSelection (api.distance before) (api.settled before) selected
  represents : ∀ target weight, (target, weight) ∈ adjacency selected ↔ edge selected target weight
  scan : RelaxScan (settleVertex (api.settled before) selected) selected
    (adjacency selected) (api.distance before) (api.distance after)
  settled : api.settled after = settleVertex (api.settled before) selected
  continuation : ∀ final, api.completion after final → api.completion before final
  cost : api.accounting before after 1 (adjacency selected).length

/-- The queue either proves exhaustion or supplies one local iteration. -/
inductive Progress {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (state : State) (remaining : List Int) : Prop where
  | done (exhausted : Exhausted (api.distance state) (api.settled state))
      (complete : api.completion state state) : Progress api edge adjacency state remaining
  | next {after : State} {selected : Int}
      (iteration : Iteration api edge adjacency state after remaining selected) :
      Progress api edge adjacency state remaining

/-- A complete compiled continuation, an independently reusable logical search
    run, and the accumulated local accounting. Final invariants are retained. -/
structure Completed {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (before after : State) (remaining : List Int) : Prop where
  invariant : ∃ pending, api.invariant after pending
  search : ∃ vertices, SearchRun edge adjacency (api.distance before) (api.settled before)
    (api.distance after) vertices ∧ ∀ vertex ∈ vertices, vertex ∈ remaining
  cost : api.accounting before after remaining.length (edgeBudget adjacency remaining)
  execution : api.completion before after



end Algo2Lean.Dijkstra.Execution


