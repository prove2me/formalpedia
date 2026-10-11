-- Prove2me | Definitions.Def_IntMul_CarryBatch
-- name    : IntMul_CarryBatch
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T12:50:49.901391+00:00
-- url     : https://prove2.me/theorems/4ed20f7b-789b-4381-944e-dbb187aba583
-- title:
--   Actual finite coefficient-list carry driver with charged boundary restarts
-- statement:
--   One fixed fifteen-tape machine traverses equal-width coefficient words from an explicit prepared caller frame. It reuses the exact native reusable-carry finite state space and transition table. The initial descriptor-return state charges two real marker/return transitions before a boundary dispatch. Subsequent charged finite-caller returns inspect the actual scanned root symbol: a bit restarts the reusable carry update, and the separator globally halts. The pure scanWords specification records emitted low digits and final carry, including empty lists. No input-length or list oracle occurs in the table. All incoming descriptors and cursors are explicit; full loop correctness, clocks, and mathematical carry-scan agreement are separate proof obligations.
-- source:
--   Original complete finite coefficient-list carry driver using actual reusable arithmetic/cleanup and charged scanned-symbol restarts. Written by Codex.

import Definitions.Def_IntMul_ReusableCarryStep

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CarryBatch
open TapeCopy (Sym)
open TapeAdder (safeStep)

/-- The complete bit-level carry traversal, retaining the final canonical
carry word. This is the proof specification, not an operation in the table. -/
def scanWords (z : List Bool) : List (List Bool) → List Bool → List Bool × List Bool
  | [],y => ([],y)
  | x::xs,y =>
      let rest := scanWords z xs (PaddedCarryStep.nextCarryWord x y z)
      (CarryStep.digitWord x y z++rest.1,rest.2)

abbrev State := ReusableCarryStep.machine.K

/-- Reuse the exact arithmetic machine table and finite states. The initial
state is its descriptor-return state, which performs two real marker/return
transitions before the boundary dispatcher. No extra copy of its state space
or transition table is introduced. -/
noncomputable abbrev subroutine : MultitapeTM :=
  {ReusableCarryStep.machine with
    qStart := some (.descriptor,ReusableCarryStep.relayState .seekDescriptor)
    start_ne_halt := Option.some_ne_none _}

/-- One charged boundary dispatch reads the actual next root symbol. It
restarts the actual update on a bit and globally halts on the separator. -/
noncomputable def dispatch (_phase : Unit) (a : Fin 15 → Sym) : Option (Unit × State) :=
  if a 0=.zero ∨ a 0=.one then some ((),ReusableCarryStep.machine.qStart) else none

noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Unit () dispatch

/-- Prepared coefficient list and saved carry, with the same real descriptor,
width templates and interior input/output cursors as the streaming update. -/
noncomputable def initialFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := (StreamCarryStep.initialFrame pre [] xs.flatten a y z l).cells
  head := (StreamCarryStep.initialFrame pre [] xs.flatten a y z l).head

/-- Complete coefficient-list output and retained final carry; all disposable
banks are empty with zero heads and both width templates remain restored. -/
noncomputable def finalFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then StreamCarryStep.rootTape pre [] xs.flatten l
    else if i=1 then machine.tapeOf ((a++(scanWords z xs y).1).map machine.bitSym)
    else if i=6 then machine.tapeOf (z.map machine.bitSym)
    else if i=12 then machine.tapeOf ((scanWords z xs y).2.map machine.bitSym)
    else if i=13 ∨ i=14 then StreamCarryStep.descriptorTape l else machine.tapeOf []
  head := fun i => if i=0 then pre.length+xs.flatten.length+1
    else if i=1 then a.length+(scanWords z xs y).1.length+1
    else if i=13 ∨ i=14 then l.length+1 else 0

end IntMul.CarryBatch


