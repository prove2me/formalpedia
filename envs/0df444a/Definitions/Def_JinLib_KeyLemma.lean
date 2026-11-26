-- Prove2me | Definitions.Def_JinLib_KeyLemma
-- name    : JinLib_KeyLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:51:30.249701+00:00
-- url     : https://prove2.me/theorems/4f803eec-b73f-4364-8ee7-85863306dd87
-- title:
--   Key Lemma
-- statement:
--   Definitions and structural lemmas for Key Lemma, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
def sig (r : Fin 5) (s : Bool) (i : Fin 5) : Fin 5 := if s then r - i else r + i
variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
end DenseTriangleFree


