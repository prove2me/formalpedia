-- Prove2me | Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveLeft
-- name    : CountingMatroid_Bridge_BinaryTapeMoveLeft
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:57:29.921694+00:00
-- url     : https://prove2.me/theorems/f66d0f74-446c-434d-aa51-4107f123d410
-- title:
--   Fixed binary tape move to the left
-- statement:
--   Represent a tape by two stacks: the left stack contains cells left of the head in reverse order, and the right stack begins with the current cell. An empty stack denotes a blank cell. A fixed program moves the head left, transferring the old current cell and the previous left-side cell into the right stack in their new order.
-- source:
--   Lean 4.33.1 verified register-machine component for a deterministic binary-tape simulation.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Move a binary tape head one cell to the left in the two-stack encoding.
Register 6 is the reversed left side and register 7 begins at the current
cell. Missing cells on either side are interpreted as blank false cells. -/
def binaryTapeMoveLeftProgram : Program 0 17 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨7, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
  | 1 => .pop ⟨6, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩
  | 2 => .pop ⟨6, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩
  | 3 => .pop ⟨6, by omega⟩ ⟨6, by omega⟩ ⟨6, by omega⟩ ⟨7, by omega⟩
  | 4 => .push ⟨7, by omega⟩ false ⟨8, by omega⟩
  | 5 => .push ⟨7, by omega⟩ false ⟨9, by omega⟩
  | 6 => .push ⟨7, by omega⟩ true ⟨10, by omega⟩
  | 7 => .push ⟨7, by omega⟩ true ⟨11, by omega⟩
  | 8 => .push ⟨7, by omega⟩ false ⟨12, by omega⟩
  | 9 => .push ⟨7, by omega⟩ true ⟨13, by omega⟩
  | 10 => .push ⟨7, by omega⟩ false ⟨14, by omega⟩
  | 11 => .push ⟨7, by omega⟩ true ⟨15, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


