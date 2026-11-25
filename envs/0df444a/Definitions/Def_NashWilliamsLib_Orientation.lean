-- Prove2me | Definitions.Def_NashWilliamsLib_Orientation
-- name    : NashWilliamsLib_Orientation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:54:21.126587+00:00
-- url     : https://prove2.me/theorems/2f452d17-7d54-59b6-bfc6-623e5b9cf933
-- title:
--   Orientation
-- statement:
--   Definitions and structural lemmas for Orientation, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
def lv (p : V × V) (b : Bool) (S : Finset V) : ℕ := if Leaves p b S then 1 else 0
def liftO (s : V) (ends : ι → V × V) (o1 : ι → Bool) (i j : ι) (l : ι) : Bool :=
  if l = i then (if (ends i).2 = s then o1 i else !o1 i)
  else if l = j then (if (ends j).1 = s then o1 i else !o1 i)
  else o1 l
end NashWilliams


