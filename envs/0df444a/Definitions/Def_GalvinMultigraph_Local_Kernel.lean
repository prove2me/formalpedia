-- Prove2me | Definitions.Def_GalvinMultigraph_Local_Kernel
-- name    : GalvinMultigraph_Local_Kernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:37:41.671489+00:00
-- url     : https://prove2.me/theorems/73d6d45e-0e25-4162-b309-41f65d1098f8
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Kernel.lean

module
public import Definitions.Def_GalvinLib_Kernel
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GalvinMultigraph.Local
variable {V : Type*} [Fintype V]
def IsKernelOn (A : V → V → Prop) (S K : Finset V) : Prop :=
  K ⊆ S ∧ (∀ x ∈ K, ∀ y ∈ K, ¬ A x y) ∧ ∀ x ∈ S, x ∉ K → ∃ y ∈ K, A x y
end GalvinMultigraph.Local


