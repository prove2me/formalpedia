-- Prove2me | Definitions.Def_LeanPool_Vizing_Endpoints
-- name    : LeanPool_Vizing_Endpoints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:41:24.708903+00:00
-- url     : https://prove2.me/theorems/5ee971ed-c8e9-4154-9af9-8b26aae31f6b
-- title:
--   Endpoints
-- statement:
--   Definitions and structural lemmas for Endpoints, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Endpoints.lean

module
public import Definitions.Def_LeanPool_Vizing_Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace LeanPool.Vizing
variable {V : Type*} [Fintype V] [DecidableEq V]
end LeanPool.Vizing


