-- Prove2me | Definitions.Def_JinLib_Patterns
-- name    : JinLib_Patterns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:49:59.058544+00:00
-- url     : https://prove2.me/theorems/b896a0aa-1234-4caf-8339-3b50de2a5e72
-- title:
--   Patterns
-- statement:
--   Definitions and structural lemmas for Patterns, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Patterns.lean

module
public import Mathlib
public import Definitions.Def_JinLib_Pairs
public import Definitions.Def_JinLib_Maximal
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
  (hδ : 10 * Fintype.card V < 29 * G.minDegree)
include h3 hmax hδ
end DenseTriangleFree


