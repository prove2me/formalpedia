-- Prove2me | Definitions.Def_CatalyticTreeEval_WhileFlag
-- name    : CatalyticTreeEval_WhileFlag
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:22:53.993598+00:00
-- url     : https://prove2.me/theorems/d95f545c-b366-4611-9db1-131b728faa83
-- title:
--   Native finite-control while loop with explicit dispatch steps
-- statement:
--   A fixed finite binary controller tests the scanned work bit. On true it dispatches a fixed body machine; the body first halts back to the controller. On false the controller halts. The controller preserves all tapes, heads and output. Dispatch and final tests each cost one actual transition; body return is folded into its halting transition. The module defines only the finite code, configuration embeddings and elapsed-time sum.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3 machine model and Section 4 uniform routine construction.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WhileFlag

open CatalyticMatching.General

def gateState (A : Machine) : Fin (1 + A.states) := finSumFinEquiv (Sum.inl 0)

def bodyState (A : Machine) (q : Fin A.states) : Fin (1 + A.states) :=
  finSumFinEquiv (Sum.inr q)

/-- A controller examines only the scanned work bit. All physical data stay put. -/
def gateInstruction (A : Machine) (work : Bool) : Instruction (1 + A.states) where
  next := if work then some (bodyState A A.start) else none
  workWrite := work
  catalystWrite := none
  inputMove := .stay
  workMove := .stay
  catalystMove := .stay
  emit := none

/-- The body's first halting transition returns to the loop controller. -/
def bodyInstruction (A : Machine) (a : Instruction A.states) : Instruction (1 + A.states) :=
  { a with next := some (a.next.elim (gateState A) (bodyState A)) }

/-- A fixed finite binary while host; no input-dependent transition table is used. -/
def machine (A : Machine) : Machine where
  states := 1 + A.states
  start := gateState A
  table q input work catalyst io wo co :=
    match finSumFinEquiv.symm q with
    | .inl _ => gateInstruction A work
    | .inr qa => bodyInstruction A (A.table qa input work catalyst io wo co)

def startBody (A : Machine) (c : Configuration A) : Configuration A :=
  { c with state := some A.start }

def bodyConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := some (c.state.elim (gateState A) (bodyState A)) }

def gateConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := some (gateState A) }

def haltConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := none }

/-- Dispatch costs one step per body call; the final false test costs one more. -/
def elapsed (time : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (1 + time i)

end CatalyticTreeEval.Contracts.WhileFlag


