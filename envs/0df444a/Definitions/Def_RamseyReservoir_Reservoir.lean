-- Prove2me | Definitions.Def_RamseyReservoir_Reservoir
-- name    : RamseyReservoir_Reservoir
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:25:55.646351+00:00
-- url     : https://prove2.me/theorems/59c728a4-f999-412a-988d-4a56cf118a9d
-- title:
--   Reservoir
-- statement:
--   Definitions and structural lemmas for Reservoir, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
structure Reservoir where
  /-- The clique built so far. -/
  spine : Finset V
  /-- The common neighbours of the spine still available. -/
  pool : Finset V
  isClique_spine : G.IsClique (spine : Set V)
  disjoint : Disjoint spine pool
  adj : ∀ x ∈ spine, ∀ y ∈ pool, G.Adj x y
namespace Reservoir
variable {G}
def ofPool (X : Finset V) : G.Reservoir where
  spine := ∅
  pool := X
  isClique_spine := by simp
  disjoint := disjoint_empty_left _
  adj := by simp
variable (R : G.Reservoir)
section Pivot
variable [DecidableRel G.Adj] [DecidableEq V]
def pivot (v : V) (hv : v ∈ R.pool) : G.Reservoir where
  spine := insert v R.spine
  pool := {w ∈ R.pool | G.Adj v w}
  isClique_spine := by
    rw [coe_insert]
    exact R.isClique_spine.insert fun b hb _ => (R.adj b hb v hv).symm
  disjoint := by
    rw [disjoint_insert_left]
    refine ⟨fun h => G.irrefl (mem_filter.mp h).2, ?_⟩
    exact R.disjoint.mono_right (filter_subset _ _)
  adj := by
    intro x hx y hy
    rw [mem_filter] at hy
    rcases mem_insert.mp hx with rfl | hx
    · exact hy.2
    · exact R.adj x hx y hy.1
variable {v : V} (hv : v ∈ R.pool)
end Pivot
section Step
variable [DecidableEq V] [DecidableRel G.Adj]
def Step (R R' : G.Reservoir) : Prop :=
  ∃ v ∈ R.pool, R'.spine = insert v R.spine ∧ R'.pool = {w ∈ R.pool | G.Adj v w}
def Reaches : G.Reservoir → G.Reservoir → Prop := Relation.ReflTransGen Step
end Step
end Reservoir
end SimpleGraph


