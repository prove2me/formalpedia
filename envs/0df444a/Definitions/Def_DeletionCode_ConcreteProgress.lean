-- Prove2me | Definitions.Def_DeletionCode_ConcreteProgress
-- name    : DeletionCode_ConcreteProgress
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:08:50.462752+00:00
-- url     : https://prove2.me/theorems/a7913a86-a206-4fcf-8a39-881ad56ca23f
-- title:
--   Concrete Progress
-- statement:
--   Definitions and structural lemmas for Concrete Progress, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteProgress.lean

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteTransitions
set_option autoImplicit true
namespace DeletionCode.ConcreteProgress
open Windows HeaderRecovery PartialWords SelectedWindows PathMemory
open ConcreteModel ConcreteDecoder ConcreteStart ConcreteFill ConcreteTransitions Recovery
variable {B : Type*} [DecidableEq B] {x : Letters} {n k : ℕ}
end DeletionCode.ConcreteProgress


