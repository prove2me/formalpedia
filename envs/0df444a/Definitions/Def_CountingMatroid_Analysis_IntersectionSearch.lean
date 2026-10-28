-- Prove2me | Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
-- name    : CountingMatroid_Analysis_IntersectionSearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:36.611918+00:00
-- url     : https://prove2.me/theorems/237d0634-6aae-4368-bb74-de9fbe9166a8
-- title:
--   Bounded exchange-graph search and intersection routine
-- statement:
--   Let $G=\{0,\ldots,n-1\}$ and let $o_1,o_2$ be Boolean functions on subsets of $G$. For a current subset $I$, the exchange graph has source and sink flags
--   $$
--   S_I(v)=[v\notin I\ \land\ o_1(I\cup\{v\})],\qquad
--   T_I(v)=[v\notin I\ \land\ o_2(I\cup\{v\})],
--   $$
--   and directed edges
--   $$
--   E_I(u,v)=[u\in I,\ v\notin I,\ o_1((I\setminus\{u\})\cup\{v\})]
--   \ \lor\
--   [u\notin I,\ v\in I,\ o_2((I\setminus\{v\})\cup\{u\})].
--   $$
--   Brackets mean the conjunction of the listed Boolean conditions. Both oracle queries are executed when testing a terminal or an edge. The tabulation routine allocates a table, evaluates entries in ground-set order, and charges table storage according to its supplied entry width.
--
--   A path table assigns each vertex either no path or a reversed vertex list. Initially each source has its singleton path. A relaxation preserves an already reached vertex and otherwise chooses the first predecessor with a stored path and an edge to the vertex, prepending the vertex and truncating to $n$ entries. All vertices in one relaxation use the same previous table. After $n$ rounds, a ground-order sink scan selects a shortest stored path, with the first candidate retained on ties. One augmentation toggles membership along the selected path; if no path exists it leaves $I$ unchanged. Starting from $\varnothing$, the intersection routine performs $r$ augmentations and returns the test $|I|=r$. These definitions specify a bounded charged algorithm for arbitrary Boolean oracles; the bundle itself imposes no matroid-correctness promise.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionSearch.lean#L22-L32

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Concrete bounded exchange-graph search for the feasibility pretest. Oracle
answers are obtained only through `oracleQuery`; the graph, path tables, and
set updates are charged. Breadth-first layers use a frozen previous table,
so the first path recorded at a vertex has minimum length. Path lists are
capped at `n` entries, and the outer solver performs exactly `r` augmentations.
The elementary query specifications are proved here. The common-independence
and maximum-cardinality theorem and the uniform cost certificate belong to
separate proof files.
-/

namespace CountingMatroid.Analysis.IntersectionSearch

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: Charge allocation and each overwrite when materializing a finite
function table. `width` bounds the represented size of one table entry. -/
def tabulate {n : ℕ} {α : Type} [Inhabited α] (width : ℕ)
    (f : Fin n → Arlib.Computation.Charged Op Cell α) :
    Arlib.Computation.Charged Op Cell (Fin n → α) := do
  let initial ← Arlib.Computation.Charged.opMany (Op.word .store)
    (n * width + 1) (fun _ => (default : α))
  Arlib.Computation.Charged.foldl (fun table i => do
    let value ← f i
    Arlib.Computation.Charged.opMany (Op.word .store) (n * width + 1)
      (Function.update table i value)) (List.finRange n) initial

/-- INTERNAL: Store the source/sink flags and directed exchange arcs for one
current common independent set. First-matroid arcs go from inside to outside;
second-matroid arcs go from outside to inside.
TEXLINE: main.tex:283-289 -/
structure ExchangeGraph (n : ℕ) where
  terminals : Fin n → Bool × Bool
  edges : Fin n → Fin n → Bool

/-- INTERNAL: Test the first- and second-matroid insertion conditions defining
sources and sinks, respectively, through the original two charged oracles. -/
def testTerminal {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Bool × Bool) := do
  let present ← containsElement I i
  let candidate ← insertElement I i
  let query ← encodeQuery candidate
  let first ← oracleQuery false o₁ query
  let second ← oracleQuery true o₂ query
  let source ← Arlib.Computation.Charged.op (Op.word .band) (!present && first)
  let sink ← Arlib.Computation.Charged.op (Op.word .band) (!present && second)
  pure (source, sink)

/-- INTERNAL: Test both possible orientations of an exchange edge, using two
charged queries even when its endpoints have the wrong membership pattern. -/
def testEdge {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (u v : Fin n) :
    Arlib.Computation.Charged Op Cell Bool := do
  let inU ← containsElement I u
  let inV ← containsElement I v
  let eraseU ← Arlib.Computation.Charged.opMany (Op.word .store) (n + 1) (I.erase u)
  let firstSet ← insertElement eraseU v
  let firstQuery ← encodeQuery firstSet
  let first ← oracleQuery false o₁ firstQuery
  let eraseV ← Arlib.Computation.Charged.opMany (Op.word .store) (n + 1) (I.erase v)
  let secondSet ← insertElement eraseV u
  let secondQuery ← encodeQuery secondSet
  let second ← oracleQuery true o₂ secondQuery
  let forward ← Arlib.Computation.Charged.opMany (Op.word .band) 2
    (inU && !inV && first)
  let backward ← Arlib.Computation.Charged.opMany (Op.word .band) 2
    (!inU && inV && second)
  Arlib.Computation.Charged.op (Op.word .bor) (forward || backward)

/-- INTERNAL: Materialize the exchange graph with polynomially many original
oracle queries; no promise about the oracle functions is needed to terminate. -/
def buildGraph {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) : Arlib.Computation.Charged Op Cell (ExchangeGraph n) := do
  let terminals ← tabulate 2 (testTerminal o₁ o₂ I)
  let edges ← tabulate (n + 1) (fun u => tabulate 1 (testEdge o₁ o₂ I u))
  pure ⟨terminals, edges⟩











/-- INTERNAL: Reverse paths to all vertices; absent entries are unreached. -/
abbrev Paths (n : ℕ) := Fin n → Option (List (Fin n))

/-- INTERNAL: Initialize breadth-first paths at the source vertices. -/
def initialPaths {n : ℕ} (g : ExchangeGraph n) :
    Arlib.Computation.Charged Op Cell (Paths n) :=
  tabulate (n + 1) (fun i => do
    let terminal ← Arlib.Computation.Charged.opMany (Op.word .load) (2 * n + 1)
      (g.terminals i)
    if terminal.1 then
      Arlib.Computation.Charged.op (Op.word .store) (some [i])
    else pure none)

/-- INTERNAL: One predecessor test uses only the frozen previous layer.
New path lists are capped to `n`, so arbitrary graph answers cannot create
an unbounded representation. Shortest simple paths fit this cap. -/
def predecessorStep {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (v : Fin n) (found : Option (List (Fin n))) (u : Fin n) :
    Arlib.Computation.Charged Op Cell (Option (List (Fin n))) := do
  let done ← isSome found
  if done then pure found else
    let path ← Arlib.Computation.Charged.opMany (Op.word .load)
      (n * (n + 1) + 1) (previous u)
    let edge ← Arlib.Computation.Charged.opMany (Op.word .load)
      (n * n + 1) (g.edges u v)
    match path with
    | none => pure none
    | some p =>
      if edge then
        Arlib.Computation.Charged.opMany (Op.word .store) (n + 1)
          (some ((v :: p).take n))
      else pure none

/-- INTERNAL: Retain a vertex's first discovered path; otherwise scan all
possible predecessors in the previous layer. -/
def relaxVertex {n : ℕ} (g : ExchangeGraph n) (previous : Paths n) (v : Fin n) :
    Arlib.Computation.Charged Op Cell (Option (List (Fin n))) := do
  let old ← Arlib.Computation.Charged.opMany (Op.word .load)
    (n * (n + 1) + 1) (previous v)
  let done ← isSome old
  if done then pure old else
    Arlib.Computation.Charged.foldl (predecessorStep g previous v)
      (List.finRange n) none

/-- INTERNAL: Synchronous breadth-first layer; table writes cannot be read
until the next layer. -/
def relaxPaths {n : ℕ} (g : ExchangeGraph n) (previous : Paths n) :
    Arlib.Computation.Charged Op Cell (Paths n) :=
  tabulate (n + 1) (relaxVertex g previous)

/-- INTERNAL: Select a shortest recorded sink path, breaking ties by ground
order. The bounded list scans also terminate for arbitrary table values. -/
def sinkStep {n : ℕ} (g : ExchangeGraph n) (paths : Paths n)
    (best : Option (List (Fin n))) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Option (List (Fin n))) := do
  let terminal ← Arlib.Computation.Charged.opMany (Op.word .load) (2 * n + 1)
    (g.terminals i)
  let path ← Arlib.Computation.Charged.opMany (Op.word .load)
    (n * (n + 1) + 1) (paths i)
  if terminal.2 then
    match path with
    | none => pure best
    | some p =>
      let candidate ← Arlib.Computation.Charged.opMany (Op.word .store) (n + 1)
        (p.take n)
      match best with
      | none => pure (some candidate)
      | some q =>
        let lengths ← Arlib.Computation.Charged.opMany (Op.word .load) (2 * (n + 1))
          (candidate.length, (q.take n).length)
        let shorter ← lessThan lengths.1 lengths.2
        if shorter then pure (some candidate) else pure best
  else pure best

/-- INTERNAL: Search `n` breadth-first layers and then choose a shortest sink
path. A directed simple path on the ground uses at most `n` vertices. -/
def findPath {n : ℕ} (g : ExchangeGraph n) :
    Arlib.Computation.Charged Op Cell (Option (List (Fin n))) := do
  let initial ← initialPaths g
  let paths ← Arlib.Computation.Charged.foldl (fun paths _ => relaxPaths g paths)
    (List.range n) initial
  Arlib.Computation.Charged.foldl (sinkStep g paths) (List.finRange n) none

/-- INTERNAL: Toggle a represented ground element, charging the membership
test and the selected set update. -/
def toggle {n : ℕ} (I : Finset (Fin n)) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Finset (Fin n)) := do
  let present ← containsElement I i
  if present then
    Arlib.Computation.Charged.opMany (Op.word .store) (n + 1) (I.erase i)
  else insertElement I i

/-- INTERNAL: One concrete shortest-exchange-path augmentation. If no path
exists it returns the current set; the progress theorem supplies maximality.
TEXLINE: main.tex:283-289 -/
def augmentOnce {n : ℕ} (o₁ o₂ : IndependenceOracle n) (I : Finset (Fin n)) :
    Arlib.Computation.Charged Op Cell (Finset (Fin n)) := do
  let graph ← buildGraph o₁ o₂ I
  let path ← findPath graph
  match path with
  | none => pure I
  | some p => Arlib.Computation.Charged.foldl toggle (p.take n) I

/-- INTERNAL: The arbitrary-rank candidate feasibility implementation. Its
loops are explicitly capped independently of any matroid or oracle promise. -/
def intersectionSolver : FeasibilityImplementation where
  run n r o₁ o₂ := do
    let I ← Arlib.Computation.Charged.foldl (fun I _ => augmentOnce o₁ o₂ I)
      (List.range r) (∅ : Finset (Fin n))
    let size ← Arlib.Computation.Charged.opMany (Op.word .load) (n + 1) I.card
    natEqual size r

end CountingMatroid.Analysis.IntersectionSearch

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r15 · construction · built capped charged exchange-graph, synchronous breadth-first search, and rank-many augmentations; proved exact query and table specifications. A three-element partition-oracle probe verified an exchange requiring removal of the current element.
-/

end


