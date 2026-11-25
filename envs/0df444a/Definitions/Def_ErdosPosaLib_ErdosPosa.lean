-- Prove2me | Definitions.Def_ErdosPosaLib_ErdosPosa
-- name    : ErdosPosaLib_ErdosPosa
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:30:25.198474+00:00
-- url     : https://prove2.me/theorems/6099e739-3389-55d3-9852-ed96d0a951ad
-- title:
--   Erdos Posa
-- statement:
--   Definitions and structural lemmas for Erdos Posa, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
universe u
def HasDisjointCycles {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Fin k → Set V, Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    ∀ i, ¬ (G.induce (S i)).IsAcyclic
def IsFeedbackSet {V : Type u} (G : SimpleGraph V) (X : Set V) : Prop :=
  (G.induce Xᶜ).IsAcyclic
end ErdosPosa


