-- Prove2me | Definitions.Def_DeletionCode_ConcreteRecovery
-- name    : DeletionCode_ConcreteRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:09:23.991749+00:00
-- url     : https://prove2.me/theorems/81e87e50-cf6c-4a33-97df-a6348df53b5a
-- title:
--   Concrete Recovery
-- statement:
--   Definitions and structural lemmas for Concrete Recovery, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteRecovery.lean

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
set_option autoImplicit true
namespace DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}
end DeletionCode.ConcreteRecovery


