-- Prove2me | Definitions.Def_JinLib_Bipartite
-- name    : JinLib_Bipartite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:53:02.83891+00:00
-- url     : https://prove2.me/theorems/99335eac-f327-56b6-a32c-2e7bcaf9bf9f
-- title:
--   Bipartite
-- statement:
--   Definitions and structural lemmas for Bipartite, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
end DenseTriangleFree


