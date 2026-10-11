-- Prove2me | Definitions.Def_Algo_kruskal_input_Analysis
-- name    : Algo_kruskal_input_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:41.630573+00:00
-- url     : https://prove2.me/theorems/ba4459bd-a0ea-4d4a-a9bd-856f44a33dd6
-- title:
--   Kruskal finite input graph and well-formedness
-- statement:
--   `KruskalInput.WellFormed` requires nonnegative vertex/edge counts and in-range endpoints for every input edge identifier. `edges` turns the finite endpoint/weight prefixes into mathematical edges with distinct identifiers, retaining arbitrary integer weights. The correspondence between a sorted identifier permutation and sorted edge data connects the sorter to the pure graph theorem.
--
--   Allocation of the source arrays is a separate generated `ValidInput` premise of the mutable call theorem. Input source, target and weight arrays need not be pairwise distinct because the algorithm only reads them.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal_input.lean

import Definitions.Def_Algo_sort_indices_Analysis
import Definitions.Def_Algo2LeanLib_KruskalMath

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The graph supplied to the source program consists of three integer sequences
and a finite edge count. This module translates that representation into the
finite graph model and connects the reusable sorting theorem to Kruskal's scan.
-/

open Algo2LeanGenerated Algo2Lean.Kruskal

namespace KruskalInput

/-- Endpoints lie in the declared vertex range. Weights need no restriction;
    parallel edges, self-loops, and negative weights are valid inputs. -/
structure WellFormed (size count : Int) (sources targets : Seq) : Prop where
  size_nonnegative : 0 ≤ size
  count_nonnegative : 0 ≤ count
  source_bounds : ∀ edge, 0 ≤ edge → edge < count → 0 ≤ sources edge ∧ sources edge < size
  target_bounds : ∀ edge, 0 ≤ edge → edge < count → 0 ≤ targets edge ∧ targets edge < size

/-- Each finite input position names one edge occurrence. -/
def edgeAt (sources targets weights : Seq) (identifier : Int) : Edge :=
  ⟨identifier.toNat, sources identifier, targets identifier, weights identifier⟩

/-- The mathematical graph retains the input's original occurrence order. -/
def edges (sources targets weights : Seq) (count : Int) : List Edge :=
  (Algo2Lean.FiniteIndex.range count).map (edgeAt sources targets weights)

@[simp] theorem edges_length (sources targets weights : Seq) (count : Int) :
    (edges sources targets weights count).length = count.toNat := by
  simp [edges]

@[simp] theorem edges_ids (sources targets weights : Seq) (count : Int) :
    (edges sources targets weights count).map Edge.id = List.range count.toNat := by
  simp [edges, Algo2Lean.FiniteIndex.range, List.map_map, Function.comp_def, edgeAt]







/-- The sorted occurrence list agrees with the returned identifier sequence.
    Its fields contain only finite graph facts and sequence observations. -/
structure SortedEdges (sources targets weights order : Seq) (count : Int)
    (pending : List Edge) : Prop where
  permutation : (edges sources targets weights count).Perm pending
  sorted : Sorted pending
  length : pending.length = count.toNat
  order : ∀ (index : Nat) (within : index < pending.length),
    order index = (pending[index].id : Int)
  source : ∀ edge ∈ pending, sources edge.id = edge.source
  target : ∀ edge ∈ pending, targets edge.id = edge.target
  weight : ∀ edge ∈ pending, weights edge.id = edge.weight
  bounded : ∀ edge ∈ pending, (edge.id : Int) < count












end KruskalInput


