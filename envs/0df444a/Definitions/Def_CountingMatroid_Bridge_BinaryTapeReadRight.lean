-- Prove2me | Definitions.Def_CountingMatroid_Bridge_BinaryTapeReadRight
-- name    : CountingMatroid_Bridge_BinaryTapeReadRight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T19:27:22.870201+00:00
-- url     : https://prove2.me/theorems/9685e7a1-a208-4b38-9b7b-ee75f8cd7601
-- title:
--   Read the current bit from the right tape stack
-- statement:
--   For a binary tape represented by a left stack and a right stack, the current symbol is the head of the right stack; when that stack is empty, the current symbol is blank. This definition provides a fixed register program that inspects this cell and restores the stack unchanged.
-- source:
--   Lean 4.33.1 fixed-register read operation aligned with the two-stack tape semantics.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Read the current tape cell from register 7, the right stack in the
two-stack tape representation. The stack is restored exactly. -/
def binaryTapeReadRightProgram : Program 1 5 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨7, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
  | 2 => .push ⟨7, by omega⟩ false ⟨4, by omega⟩
  | 3 => .push ⟨7, by omega⟩ true ⟨5, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


