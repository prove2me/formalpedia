-- Prove2me | Definitions.Def_DegreeSequences_Solution
-- name    : DegreeSequences_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:36:53.652921+00:00
-- url     : https://prove2.me/theorems/71022d62-eabd-494c-b801-765b2290fbc2
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/degree-sequences; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphic sequences: the Erdos-Gallai and Havel-Hakimi theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/Solution.lean

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace GraphicSequences
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), ∀ i, G.degree i = d i
def havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun j => if j.val < d 0 then d j.succ - 1 else d j.succ
end GraphicSequences


