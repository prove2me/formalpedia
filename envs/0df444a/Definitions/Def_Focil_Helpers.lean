-- Prove2me | Definitions.Def_Focil_Helpers
-- name    : Focil_Helpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:43.118206+00:00
-- url     : https://prove2.me/theorems/6fdacea5-ba30-4be1-935d-e03d01837c4e
-- title:
--   Helpers
-- statement:
--   Definitions and structural lemmas for Helpers, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Helpers.lean

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
set_option autoImplicit false
namespace Focil
def StoredHonestly (state : FocilState) (il : InclusionList) : Prop :=
  il ∈ state.stored_ils ∧ IsConsidered state il
end Focil


