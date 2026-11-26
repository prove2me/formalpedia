-- Prove2me | Definitions.Def_JinLib_Pairs
-- name    : JinLib_Pairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:46:42.631798+00:00
-- url     : https://prove2.me/theorems/e7982ac2-7cc0-4987-9685-70e419e680d7
-- title:
--   Pairs
-- statement:
--   Definitions and structural lemmas for Pairs, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Pairs.lean

module
public import Mathlib
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
def IsPair (a : V) (U : Fin 5 → V) : Prop :=
  (∀ i, G.Adj (U i) (U (i + 1))) ∧ ∀ i, ¬ G.Adj a (U i)
open Classical in
/-- Indices `i` such that a neighbour of `a` sees both `U (i - 1)` and `U (i + 1)`. -/
noncomputable def sSet (a : V) (U : Fin 5 → V) : Finset (Fin 5) :=
  Finset.univ.filter fun i => ∃ t, G.Adj a t ∧ G.Adj (U (i - 1)) t ∧ G.Adj (U (i + 1)) t
end DenseTriangleFree


