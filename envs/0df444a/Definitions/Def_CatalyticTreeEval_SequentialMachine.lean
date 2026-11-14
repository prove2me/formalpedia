-- Prove2me | Definitions.Def_CatalyticTreeEval_SequentialMachine
-- name    : CatalyticTreeEval_SequentialMachine
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:40:26.04499+00:00
-- url     : https://prove2.me/theorems/376b8feb-cf41-44ba-8294-64b91aa3cfe3
-- title:
--   Finite native sequential composition
-- statement:
--   Redirection of the halting transition of the first finite binary machine to the entry state of the second, preserving every tape action and emitted bit. State embeddings and physical configuration maps make the exact handoff explicit.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Sections 3.1/4 and Appendix B. Native composition adapts the shared-tape halting-redirection construction of tcslib/cslib.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.Sequential

open CatalyticMatching.General

def leftState (A B : Machine) (q : Fin A.states) : Fin (A.states + B.states) :=
  finSumFinEquiv (Sum.inl q)

def rightState (A B : Machine) (q : Fin B.states) : Fin (A.states + B.states) :=
  finSumFinEquiv (Sum.inr q)

/-- Redirect A's halting transition to B's initial state. All tape actions and
emission remain those of A; the handoff is folded into that transition. -/
def leftInstruction (A B : Machine) (a : Instruction A.states) :
    Instruction (A.states + B.states) :=
  { a with next := some (a.next.elim (rightState A B B.start) (leftState A B)) }

def rightInstruction (A B : Machine) (a : Instruction B.states) :
    Instruction (A.states + B.states) :=
  { a with next := a.next.map (rightState A B) }

/-- Native finite-table sequential composition on the same physical tapes.
It neither initializes B's work tape nor resets any head. -/
def machine (A B : Machine) : Machine where
  states := A.states + B.states
  start := leftState A B A.start
  table q input work catalyst io wo co :=
    match finSumFinEquiv.symm q with
    | .inl qa => leftInstruction A B (A.table qa input work catalyst io wo co)
    | .inr qb => rightInstruction A B (B.table qb input work catalyst io wo co)

def leftConfig (A B : Machine) (c : Configuration A) : Configuration (machine A B) :=
  { c with state := some (c.state.elim (rightState A B B.start) (leftState A B)) }

def rightConfig (A B : Machine) (c : Configuration B) : Configuration (machine A B) :=
  { c with state := c.state.map (rightState A B) }

/-- B begins on exactly A's final tapes, heads and output. -/
def handoff (A B : Machine) (c : Configuration A) : Configuration B :=
  { c with state := some B.start }

end CatalyticTreeEval.Contracts.Sequential


