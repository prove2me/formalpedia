-- Prove2me | Definitions.Def_LeanPool_Vizing_Step
-- name    : LeanPool_Vizing_Step
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:57:42.322347+00:00
-- url     : https://prove2.me/theorems/3bdfa442-d957-4070-9612-ddf5573ac640
-- title:
--   Step
-- statement:
--   Definitions and structural lemmas for Step, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Step.lean

module
public import Definitions.Def_LeanPool_Vizing_Fan
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace LeanPool.Vizing
namespace PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
end PEC
end LeanPool.Vizing


