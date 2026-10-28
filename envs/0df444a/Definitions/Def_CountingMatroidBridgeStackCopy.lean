-- Prove2me | Definitions.Def_CountingMatroidBridgeStackCopy
-- name    : CountingMatroidBridgeStackCopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T23:02:28.593477+00:00
-- url     : https://prove2.me/theorems/e4ac1519-91ef-4287-9063-1fdcee1d6dd2
-- title:
--   Order-preserving finite bit-stack copy machine
-- statement:
--   A fixed OAI register program copies the finite bit stack in register 6 to register 10 in the same order, while restoring register 6 and clearing scratch register 11. It uses exactly 5 times the source length plus 2 steps and bit operations, and makes no oracle calls.
-- source:
--   Lean 4.33.1 implementation with an explicit two-pass stack trace. No Arlib dependency.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Move all bits from register 6 to register 7, reversing their order. -/
def binaryStackMoveProgram : Program 1 3 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨6, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ ⟨3, by omega⟩
  | 1 => .push ⟨7, by omega⟩ false ⟨0, by omega⟩
  | 3 => .push ⟨7, by omega⟩ true ⟨0, by omega⟩
  | _ => .halt

/-- A fixed OAI routine that duplicates the little-endian bit stack in register
6 into register 10 while restoring the source. Register 11 is a temporary
reverse stack and is empty on return. The destination receives the original
bit order, followed by its previous contents. -/
def binaryStackCopyProgram : Program 5 8 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨6, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ ⟨3, by omega⟩
  | 1 => .push ⟨11, by omega⟩ false ⟨0, by omega⟩
  | 3 => .push ⟨11, by omega⟩ true ⟨0, by omega⟩
  | 2 => .pop ⟨11, by omega⟩ ⟨6, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩
  | 4 => .push ⟨6, by omega⟩ false ⟨7, by omega⟩
  | 5 => .push ⟨6, by omega⟩ true ⟨8, by omega⟩
  | 7 => .push ⟨10, by omega⟩ false ⟨2, by omega⟩
  | 8 => .push ⟨10, by omega⟩ true ⟨2, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


