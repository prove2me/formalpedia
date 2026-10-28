-- Prove2me | Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveRight
-- name    : CountingMatroid_Bridge_BinaryTapeMoveRight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:50:43.804121+00:00
-- url     : https://prove2.me/theorems/82b95946-dc76-4e57-a1a5-0676ac829d0e
-- title:
--   Fixed binary tape move to the right
-- statement:
--   Represent a tape by two stacks: the left stack contains cells left of the head in reverse order, and the right stack begins with the current cell. An empty right stack denotes a blank cell. A fixed program moves the head right, transferring the old cell to the left stack and exposing the suffix as the new right stack.
-- source:
--   Lean 4.33.1 verified register-machine component for a deterministic binary-tape simulation.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Move a binary tape head one cell to the right. Register 6 stores the cells
left of the head in reverse order; register 7 stores the current cell followed
by the cells to its right. An empty right stack denotes a blank current cell. -/
def binaryTapeMoveRightProgram : Program 0 6 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨7, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
  | 1 => .push ⟨6, by omega⟩ false ⟨5, by omega⟩
  | 2 => .push ⟨6, by omega⟩ false ⟨5, by omega⟩
  | 3 => .push ⟨6, by omega⟩ true ⟨6, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


