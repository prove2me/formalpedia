-- Prove2me | Definitions.Def_Konig_Basic
-- name    : Konig_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:04:35.740393+00:00
-- url     : https://prove2.me/theorems/ae290fd6-1771-4af1-877a-8d59244722bf
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean

module
public import Definitions.Def_LeanPool_Vizing_Main
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
end Konig


