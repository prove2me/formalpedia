-- Prove2me | Definitions.Def_ErdosPosaCycles_Solution
-- name    : ErdosPosaCycles_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:31:23.131813+00:00
-- url     : https://prove2.me/theorems/45dc96bf-177c-58c3-90b9-92009b1af410
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace CyclePacking
universe u
def HasDisjointCycles {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Fin k → Set V, Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    ∀ i, ¬ (G.induce (S i)).IsAcyclic
def IsFeedbackSet {V : Type u} (G : SimpleGraph V) (X : Set V) : Prop :=
  (G.induce Xᶜ).IsAcyclic
end CyclePacking


