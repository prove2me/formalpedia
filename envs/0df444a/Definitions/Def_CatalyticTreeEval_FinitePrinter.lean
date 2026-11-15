-- Prove2me | Definitions.Def_CatalyticTreeEval_FinitePrinter
-- name    : CatalyticTreeEval_FinitePrinter
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T06:25:44.396203+00:00
-- url     : https://prove2.me/theorems/5bd5fc7b-c871-4ccd-8335-b92aeca017db
-- title:
--   Finite configuration keys for native space-bounded printers
-- statement:
--   For a fixed native binary printer with an empty catalyst, erase its unreadable output history. A configuration using fewer than b addressed work cells is then described by its control, its input-head position, its work-head position and its b work bits. For input length n and s control states the number of such keys is $$(s+1)(n+2)b2^b.$$ The omitted work suffix is required to remain blank. This finite quotient supports explicit time bounds for space-bounded printing without changing the machine.
-- source:
--   Infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, native printing predicates and uniform access routines.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.FinitePrinter

open CatalyticMatching.General

/-- A semantic quotient used only for counting: output is not readable by the
native transition table, so its history need not be part of a configuration key. -/
def eraseOutput {M : Machine} (c : Configuration M) : Configuration M :=
  { c with output := [] }

def quietStep (M : Machine) (input : List Bool) (c : Configuration M) :
    Option (Configuration M) := (M.step input c).map eraseOutput

/-- The finite information in a bounded printer run, with an empty catalyst. -/
abbrev PrinterCore (M : Machine) (inputLength bound : ℕ) :=
  Option (Fin M.states) × Fin (inputLength + 2) × Fin bound × (Fin bound → Bool)

def core (M : Machine) (inputLength bound : ℕ) (c : Configuration M)
    (hi : c.inputHead ≤ inputLength + 1) (hw : c.workHead < bound) :
    PrinterCore M inputLength bound :=
  ⟨c.state, ⟨c.inputHead, by omega⟩, ⟨c.workHead, hw⟩, fun p => c.work p.val⟩

def configurationBound (M : Machine) (inputLength bound : ℕ) : ℕ :=
  (M.states + 1) * (inputLength + 2) * bound * 2 ^ bound

end CatalyticTreeEval.Contracts.FinitePrinter


