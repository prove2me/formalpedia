-- Prove2me | Definitions.Def_NashWilliamsLib_Mader
-- name    : NashWilliamsLib_Mader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:49:32.78081+00:00
-- url     : https://prove2.me/theorems/425eb6e4-1d17-5df9-acde-1c00a46b2df0
-- title:
--   Mader
-- statement:
--   Definitions and structural lemmas for Mader, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean

module
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
def Tight (K : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι) (S : Finset V) : Prop :=
  S ⊆ T ∧ S.Nonempty ∧ S ≠ T ∧ cutF ends F S = K
end NashWilliams


