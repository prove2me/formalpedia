-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
-- name    : LeanPool_K5MinorFreeChoosability_Planar_Hypermap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:14:36.639215+00:00
-- url     : https://prove2.me/theorems/d517d710-a972-5057-b770-0de4cf95abe0
-- title:
--   Hypermap
-- statement:
--   Definitions and structural lemmas for Hypermap, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
def compSetoid (σ α : Perm D) : Setoid D where
  r := Relation.EqvGen (fun a b => b = σ a ∨ b = α a)
  iseqv := Relation.EqvGen.is_equivalence _
noncomputable def numComponents (σ α : Perm D) : ℕ := numClasses (compSetoid σ α)
noncomputable def eulerDefect (σ α : Perm D) : ℤ :=
  (Nat.card D : ℤ) + 2 * (numComponents σ α : ℤ) - cycleCount σ - cycleCount α -
    cycleCount (σ * α)
section Swap
variable [DecidableEq D]
variable [Finite D]
end Swap
section Subtype
variable (p : D → Prop) [DecidablePred p]
end Subtype
end LeanPool.K5MinorFreeChoosability


