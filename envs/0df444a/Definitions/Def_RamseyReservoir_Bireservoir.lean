-- Prove2me | Definitions.Def_RamseyReservoir_Bireservoir
-- name    : RamseyReservoir_Bireservoir
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:28:05.378151+00:00
-- url     : https://prove2.me/theorems/ebbb13ba-64c9-4e94-ac4c-8235301f1ebc
-- title:
--   Bireservoir
-- statement:
--   Definitions and structural lemmas for Bireservoir, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
structure Bireservoir where
  /-- The red spine, a clique of `G`. -/
  red : Finset V
  /-- The blue spine, a clique of `Gᶜ`. -/
  blue : Finset V
  /-- The common pool. -/
  pool : Finset V
  isClique_red : G.IsClique (red : Set V)
  isClique_blue : Gᶜ.IsClique (blue : Set V)
  disjoint_red : Disjoint red pool
  disjoint_blue : Disjoint blue pool
  adj_red : ∀ x ∈ red, ∀ y ∈ pool, G.Adj x y
  adj_blue : ∀ x ∈ blue, ∀ y ∈ pool, Gᶜ.Adj x y
namespace Bireservoir
variable {G}
def ofPool (X : Finset V) : G.Bireservoir where
  red := ∅
  blue := ∅
  pool := X
  isClique_red := by simp
  isClique_blue := by simp
  disjoint_red := disjoint_empty_left _
  disjoint_blue := disjoint_empty_left _
  adj_red := by simp
  adj_blue := by simp
variable (S : G.Bireservoir)
def toRed : G.Reservoir := ⟨S.red, S.pool, S.isClique_red, S.disjoint_red, S.adj_red⟩
def toBlue : Gᶜ.Reservoir := ⟨S.blue, S.pool, S.isClique_blue, S.disjoint_blue, S.adj_blue⟩
section Pivot
variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)
def redPivot : G.Bireservoir where
  red := insert v S.red
  blue := S.blue
  pool := {w ∈ S.pool | G.Adj v w}
  isClique_red := (S.toRed.pivot v hv).isClique_spine
  isClique_blue := S.isClique_blue
  disjoint_red := (S.toRed.pivot v hv).disjoint
  disjoint_blue := S.disjoint_blue.mono_right (filter_subset _ _)
  adj_red := (S.toRed.pivot v hv).adj
  adj_blue x hx y hy := S.adj_blue x hx y (mem_filter.mp hy).1
def bluePivot : G.Bireservoir where
  red := S.red
  blue := insert v S.blue
  pool := {w ∈ S.pool | Gᶜ.Adj v w}
  isClique_red := S.isClique_red
  isClique_blue := (S.toBlue.pivot v hv).isClique_spine
  disjoint_red := S.disjoint_red.mono_right (filter_subset _ _)
  disjoint_blue := (S.toBlue.pivot v hv).disjoint
  adj_red x hx y hy := S.adj_red x hx y (mem_filter.mp hy).1
  adj_blue := (S.toBlue.pivot v hv).adj
end Pivot
def IsWinning (R : ℕ → ℕ → ℕ) (r s : ℕ) : Prop :=
  R (r - #S.red) (s - #S.blue) ≤ #S.pool
def _root_.SimpleGraph.IsPascal (R : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b, R a (b + 1) + R (a + 1) b ≤ R (a + 1) (b + 1) ∧ 0 < R (a + 1) (b + 1)
variable {S}
end Bireservoir
end SimpleGraph


