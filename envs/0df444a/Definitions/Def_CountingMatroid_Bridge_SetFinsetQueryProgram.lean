-- Prove2me | Definitions.Def_CountingMatroid_Bridge_SetFinsetQueryProgram
-- name    : CountingMatroid_Bridge_SetFinsetQueryProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T16:39:51.978824+00:00
-- url     : https://prove2.me/theorems/83ab2667-e89b-4dad-befa-fa7d96d9995c
-- title:
--   Setter followed by an exact independence-oracle query
-- statement:
--   A fixed binary-register program updates one element of a finite-set membership vector and immediately queries the resulting set with the selected independence oracle. Its branch is exactly the selected matroid independence predicate, it preserves the canonical vector, clears scratch registers, makes one oracle call, and has exact bit-operation cost.
-- source:
--   Lean 4.33.1 program composition on the existing mission machine, using the verified indexed setter. No Arlib dependency.

import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- The fixed indexed-setter code followed by one independence-oracle query.
The setter terminates at state 11; that return state is reused for the query.
Its remaining states distinguish the false and true oracle branches. -/
def setFinsetQueryProgram (value which : Bool) : Program 2 11 := fun pc =>
  if h : pc.val = 11 then
    .query which ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨11, by omega⟩
  else
    setMembershipBitProgram value ⟨11, by omega⟩ pc

end CountingMatroid.Bridge


