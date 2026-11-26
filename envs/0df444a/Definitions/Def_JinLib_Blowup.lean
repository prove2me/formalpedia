-- Prove2me | Definitions.Def_JinLib_Blowup
-- name    : JinLib_Blowup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:46:30.866369+00:00
-- url     : https://prove2.me/theorems/297d1af8-199d-440a-a5f9-e371e77dfe01
-- title:
--   Blowup
-- statement:
--   Definitions and structural lemmas for Blowup, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Blowup.lean

module
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
def slotProj (k : Fin 29) : Fin 11 :=
  if k.val < 15 then ⟨k.val / 3, by omega⟩
  else if h : k.val < 25 then ⟨5 + (k.val - 15) / 2, by omega⟩ else 10
def blowProj (m : ℕ) (a : Fin (29 * m)) : Fin 11 := slotProj (finProdFinEquiv.symm a).1
def blowup (m : ℕ) : SimpleGraph (Fin (29 * m)) := grotzsch.comap (blowProj m)
instance (m : ℕ) : DecidableRel (blowup m).Adj := fun a b =>
  inferInstanceAs (Decidable (grotzsch.Adj (blowProj m a) (blowProj m b)))
end DenseTriangleFree


