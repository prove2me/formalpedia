-- Prove2me | Definitions.Def_CountingMatroid_Bridge_BinaryTapeRead
-- name    : CountingMatroid_Bridge_BinaryTapeRead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:43:18.9981+00:00
-- url     : https://prove2.me/theorems/8a0a9a24-8ad4-4057-981e-2e6fca9f3249
-- title:
--   Binary tape head read with stack restoration
-- statement:
--   A fixed binary-register program reads the cell under a tape head represented by the top of a stack. An empty stack denotes a blank false cell. The program preserves the represented tape, reports an explicit false or true bit in control, and uses one instruction for a blank cell or two for an explicit bit.
-- source:
--   Lean 4.33.1 local adapter component for translating a deterministic binary tape machine into the mission register-machine model.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Read the symbol currently under a binary tape head, represented by the top
of register 6. The empty stack is interpreted as a blank (false) cell. -/
def binaryTapeReadProgram : Program 0 5 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨6, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
  | 2 => .push ⟨6, by omega⟩ false ⟨4, by omega⟩
  | 3 => .push ⟨6, by omega⟩ true ⟨5, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


