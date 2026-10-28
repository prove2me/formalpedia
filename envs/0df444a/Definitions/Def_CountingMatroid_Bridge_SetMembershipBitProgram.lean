-- Prove2me | Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram
-- name    : CountingMatroid_Bridge_SetMembershipBitProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T16:07:30.473049+00:00
-- url     : https://prove2.me/theorems/4c24f95a-29cd-462f-8b3d-9d3b641f0bbd
-- title:
--   Fixed machine program for setting one finite-set bit
-- statement:
--   For a Boolean vector representing a finite subset of [n], a fixed binary-register program overwrites the bit at a unary index and restores all other bits. Its exact charged cost is linear in the index, independent of the prior value at that position.
-- source:
--   Lean 4.33.1 finite-set representation and target Program, with no Arlib dependency. This is the concrete vector update primitive used to prepare independence-oracle queries.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Result of a fixed or toggling update of a membership bit. -/
def membershipBitResult (value toggle old : Bool) : Bool :=
  if toggle then !old else value

/-- Update one bit in a little-endian membership vector. Register 6 is the vector,
register 7 is a unary index (one `true` per skipped position), and register 8
is scratch. At state 9 the program pops an empty scratch stack and continues to
the caller-supplied state. In toggle mode the selected bit determines whether
state 5 or state 10 writes the replacement bit. -/
def membershipBitProgram (value toggle : Bool) (next : Fin 12) : Program 2 11 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨7, by omega⟩ ⟨4, by omega⟩ ⟨11, by omega⟩ ⟨1, by omega⟩
  | 1 => .pop ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
  | 2 => .push ⟨8, by omega⟩ false ⟨0, by omega⟩
  | 3 => .push ⟨8, by omega⟩ true ⟨0, by omega⟩
  | 4 => .pop ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨5, by omega⟩
      (if toggle then ⟨10, by omega⟩ else ⟨5, by omega⟩)
  | 5 => .push ⟨6, by omega⟩ (membershipBitResult value toggle false) ⟨6, by omega⟩
  | 6 => .pop ⟨8, by omega⟩ ⟨9, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩
  | 7 => .push ⟨6, by omega⟩ false ⟨6, by omega⟩
  | 8 => .push ⟨6, by omega⟩ true ⟨6, by omega⟩
  | 9 => .pop ⟨8, by omega⟩ next ⟨11, by omega⟩ ⟨11, by omega⟩
  | 10 => .push ⟨6, by omega⟩ false ⟨6, by omega⟩
  | _ => .halt

/-- Set a membership bit to a prescribed value. -/
def setMembershipBitProgram (value : Bool) (next : Fin 12) : Program 2 11 :=
  membershipBitProgram value false next

/-- Flip one membership bit. -/
def toggleMembershipBitProgram (next : Fin 12) : Program 2 11 :=
  membershipBitProgram false true next

/-- The canonical little-endian query bits of a finite set. -/
def finsetMembershipBits {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  List.ofFn fun i : Fin n => decide (i ∈ s)

end CountingMatroid.Bridge


