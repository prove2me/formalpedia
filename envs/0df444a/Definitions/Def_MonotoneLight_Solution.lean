-- Prove2me | Definitions.Def_MonotoneLight_Solution
-- name    : MonotoneLight_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:30:28.548899+00:00
-- url     : https://prove2.me/theorems/ab71f576-c46d-561a-8798-fa2f39891734
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/monotone-light-factorization-lean; see pinned Apache-2.0 LICENSE)'s pinned Monotone-light factorization of compact Hausdorff surjections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set Function Topology
universe u v
namespace MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
def FiberRel (f : X → Y) (x y : X) : Prop :=
  y ∈ connectedComponentIn (f ⁻¹' {f x}) x
omit [TopologicalSpace Y] in
theorem FiberRel.map_eq {f : X → Y} {x y : X} (h : FiberRel f x y) : f y = f x :=
  show f y ∈ ({f x} : Set Y) from
    connectedComponentIn_subset (f ⁻¹' {f x}) x h
def fiberSetoid (f : X → Y) : Setoid X where
  r := FiberRel f
  iseqv := {
    refl := fun x => mem_connectedComponentIn rfl
    symm := by
      intro x y h
      have he := h.map_eq
      change x ∈ connectedComponentIn (f ⁻¹' {f y}) y
      rw [he, ← connectedComponentIn_eq h]
      exact mem_connectedComponentIn rfl
    trans := by
      intro x y z hxy hyz
      change z ∈ connectedComponentIn (f ⁻¹' {f x}) x
      rw [connectedComponentIn_eq hxy]
      simpa only [FiberRel, hxy.map_eq] using hyz }
abbrev Middle (f : X → Y) := Quotient (fiberSetoid f)
def monotone (f : X → Y) : X → Middle f := Quotient.mk (fiberSetoid f)
def light (f : X → Y) : Middle f → Y :=
  Quotient.lift f (fun _ _ h => h.map_eq.symm)
end MonotoneLight


