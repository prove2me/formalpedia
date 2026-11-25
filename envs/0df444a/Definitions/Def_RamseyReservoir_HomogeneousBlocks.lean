-- Prove2me | Definitions.Def_RamseyReservoir_HomogeneousBlocks
-- name    : RamseyReservoir_HomogeneousBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:26:37.076938+00:00
-- url     : https://prove2.me/theorems/fcb3751f-0320-4e36-b311-1c81e13526af
-- title:
--   Homogeneous Blocks
-- statement:
--   Definitions and structural lemmas for Homogeneous Blocks, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Function
namespace SimpleGraph
variable {V ι : Type*}
structure HomogeneousBlocks (G : SimpleGraph V) (ι : Type*) where
  /-- The blocks. -/
  block : ι → Finset V
  nonempty : ∀ i, (block i).Nonempty
  pairwiseDisjoint : Pairwise (Disjoint on block)
  homogeneous : ∀ i j, i ≠ j →
    (∀ x ∈ block i, ∀ y ∈ block j, G.Adj x y) ∨ ∀ x ∈ block i, ∀ y ∈ block j, ¬G.Adj x y
namespace HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
def quotient : SimpleGraph ι :=
  fromRel fun i j => ∀ x ∈ F.block i, ∀ y ∈ F.block j, G.Adj x y
theorem ne_of_mem_block {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ F.block i)
    (hy : y ∈ F.block j) : x ≠ y := by
  rintro rfl
  exact Finset.disjoint_left.mp (F.pairwiseDisjoint hij) hx hy
noncomputable def rep (i : ι) : V := (F.nonempty i).choose
theorem rep_mem (i : ι) : F.rep i ∈ F.block i := (F.nonempty i).choose_spec
theorem rep_injective : Injective F.rep := fun i j h => by
  by_contra hij
  exact F.ne_of_mem_block hij (F.rep_mem i) (F.rep_mem j) h
noncomputable def repEmbedding : ι ↪ V := ⟨F.rep, F.rep_injective⟩
end HomogeneousBlocks
end SimpleGraph


