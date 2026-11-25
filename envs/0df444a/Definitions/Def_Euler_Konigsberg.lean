-- Prove2me | Definitions.Def_Euler_Konigsberg
-- name    : Euler_Konigsberg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:29:42.76209+00:00
-- url     : https://prove2.me/theorems/54d80ca4-6f8d-426f-b0e3-114a7e7682fb
-- title:
--   Konigsberg
-- statement:
--   Definitions and structural lemmas for Konigsberg, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Konigsberg
def edgeList : List (ℕ × ℕ) :=
  [(4, 0), (4, 1), (5, 0), (5, 1),   -- A–B (dos puentes)
   (6, 0), (6, 2), (7, 0), (7, 2),   -- A–C (dos puentes)
   (8, 0), (8, 3),                   -- A–D
   (9, 1), (9, 3),                   -- B–D
   (10, 2), (10, 3)]
def graph : SimpleGraph (Fin 11) where
  Adj i j := (i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by fin_cases i <;> decide⟩
instance : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList))
end Konigsberg


