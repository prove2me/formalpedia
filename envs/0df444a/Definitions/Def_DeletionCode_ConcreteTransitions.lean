-- Prove2me | Definitions.Def_DeletionCode_ConcreteTransitions
-- name    : DeletionCode_ConcreteTransitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:08:10.89778+00:00
-- url     : https://prove2.me/theorems/1924088c-aae5-476c-9109-877f5b4d4f4f
-- title:
--   Concrete Transitions
-- statement:
--   Definitions and structural lemmas for Concrete Transitions, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteTransitions.lean

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
namespace DeletionCode.ConcreteTransitions
open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)
variable {B : Type*}
def BankSound (mem : B → Memory) (p : B → Letters) (len : B → ℕ) : Prop :=
  ∀ b, Sound (mem b) (p b) (len b)
end DeletionCode.ConcreteTransitions


