-- Prove2me | Definitions.Def_GalvinLib_Kernel
-- name    : GalvinLib_Kernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:05.066267+00:00
-- url     : https://prove2.me/theorems/c7e3c1c9-1a5b-4d62-83f3-59b412ac99be
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Kernel.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Galvin
open Finset
def HasKernels {α : Type*} (G : SimpleGraph α) (D : α → α → Prop) : Prop :=
  ∀ S : Finset α, ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬ G.Adj x y) ∧
    ∀ x ∈ S, x ∉ K → ∃ y ∈ K, D x y
end Galvin


