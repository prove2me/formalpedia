-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_LogspaceMachine
-- name    : CommutativeRankNC_Approximation_LogspaceMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:42.663564+00:00
-- url     : https://prove2.me/theorems/7df2db67-965b-4be7-a030-9b898c9d9548
-- title:
--   Finite deterministic logspace transducers
-- statement:
--   A deterministic transducer has finite control, a read-only binary input with an end marker, a binary work tape initially zero, and a write-only binary output. An instruction reads one input symbol and one work bit, writes one work bit, moves each head by at most one cell, optionally emits one bit, and changes state or halts.
--
--   $$\operatorname{space}(M,w)\le s$$
--
--   means that a halting run exists and every visited work position has absolute value at most $s$. The input head is confined to the input and end marker, and the output cannot be read by the transition function. This fixes a genuine finite-machine meaning for uniform circuit generation; it contains no mathematical correctness condition.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), p.24 (uniform Boolean interpretation); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Mathlib

namespace CommutativeRankNC.Approximation

/-- Moves of a tape head. -/
inductive HeadMove where
  | left | stay | right
  deriving DecidableEq

/-- One finite-control instruction: two head moves, one work bit, one optional
output bit, and the next state (none halts). The output is write-only. -/
structure MachineAction (q : ℕ) where
  next : Option (Fin q)
  inputMove : HeadMove
  workMove : HeadMove
  write : Bool
  emit : Option Bool

/-- A deterministic finite program. The domain of transition is finite; it can
inspect only the current input symbol and one work bit. -/
structure LogspaceMachine where
  states : ℕ
  initial : Fin states
  transition : Fin states → Option Bool → Bool → MachineAction states

structure MachineConfiguration (M : LogspaceMachine) where
  state : Option (Fin M.states)
  inputHead : ℕ
  workHead : ℤ
  tape : ℤ → Bool
  output : List Bool

def moveWork (h : ℤ) : HeadMove → ℤ
  | .left => h - 1
  | .stay => h
  | .right => h + 1

/-- Read-only input head is confined to the input and its end marker, so it
cannot be used as an unbounded uncharged counter. -/
def moveInput (h bound : ℕ) : HeadMove → ℕ
  | .left => h - 1
  | .stay => min h bound
  | .right => min (h + 1) bound

def machineStart (M : LogspaceMachine) : MachineConfiguration M :=
  ⟨some M.initial, 0, 0, fun _ => false, []⟩

def machineStep (M : LogspaceMachine) (input : List Bool)
    (c : MachineConfiguration M) : MachineConfiguration M :=
  match c.state with
  | none => c
  | some s =>
    let a := M.transition s (input[c.inputHead]?) (c.tape c.workHead)
    ⟨a.next, moveInput c.inputHead input.length a.inputMove,
      moveWork c.workHead a.workMove, Function.update c.tape c.workHead a.write,
      c.output ++ a.emit.toList⟩

def machineRun (M : LogspaceMachine) (input : List Bool) : ℕ → MachineConfiguration M
  | 0 => machineStart M
  | t + 1 => machineStep M input (machineRun M input t)

/-- A halting computation with an explicit bound on all visited work-tape
positions. Starting at zero and moving one cell at a time, this charges the
entire used interval; the read-only input and write-only output are excluded. -/
def GeneratesWithin (M : LogspaceMachine) (input output : List Bool) (space : ℕ) : Prop :=
  ∃ T, (machineRun M input T).state = none ∧
    (machineRun M input T).output = output ∧
    ∀ t ≤ T, (machineRun M input t).workHead.natAbs ≤ space

end CommutativeRankNC.Approximation


