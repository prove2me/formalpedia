-- Prove2me | Definitions.Def_HadwigerMader_Solution
-- name    : HadwigerMader_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:40:37.649306+00:00
-- url     : https://prove2.me/theorems/2cc35d03-90db-413b-b514-9c992696ebe8
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/hadwiger-mader; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader's theorem and Hadwiger's conjecture for t at most 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace HadwigerMader
variable {V W : Type*}
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)
end HadwigerMader


