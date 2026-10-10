-- Prove2me | Definitions.Def_IntMul_CarryStep
-- name    : IntMul_CarryStep
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T09:57:33.86169+00:00
-- url     : https://prove2.me/theorems/095a38ba-3a38-467a-bffe-d212a72c4257
-- title:
--   Fixed nine-tape local bounded-carry arithmetic machine
-- statement:
--   Let x and y be equal-width binary operands and let z describe a block size B=val(z)+1. The fixed nine-tape local arithmetic machine adds x and y, physically constructs a least-significant-first sum request, extracts its first B bits through an actual countdown, and copies the remaining bits into the outgoing carry bank. Its finite table uses only state and scanned symbols. The incoming frame includes the original read-only input x#y and a descriptor bank already written by the caller; all other banks are blank and every head starts at zero. The complete terminal frame specifies the emitted low digit, outgoing carry, retained sum and operands, routed request, restored counter templates and all nine final heads. The output digit and carry are little-endian. Arithmetic correctness and the total actual transition bound are separate obligations; preparing the descriptor bank is an explicit caller responsibility.
-- source:
--   Original complete physical local carry step in the integer multiplication multitape model. Written by Codex.

import Definitions.Def_IntMul_CountedStreamFrames
import Definitions.Def_IntMul_FiniteCaller

namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive Relay
  | seekSumEnd | copySum | copyDescriptor | rewind | openCarry | copyCarry
  deriving DecidableEq

instance : Fintype Relay where
  elems := {.seekSumEnd,.copySum,.copyDescriptor,.rewind,.openCarry,.copyCarry}
  complete := by intro q; cases q <;> simp

abbrev State := Option (TapeAdder.State ⊕ (Relay ⊕ CountedStream.State))

def adderState (q : TapeAdder.State) : State :=
  if q=.halt then none else some (.inl q)

def streamState (q : CountedStream.State) : State :=
  if q=.halt then none else some (.inr (.inr q))

def relayState (q : Relay) : State := some (.inr (.inl q))

def adderTape (i : Fin 3) : Fin 9 := if i=0 then 0 else if i=1 then 2 else 3

def streamTape (i : Fin 4) : Fin 9 :=
  if i=0 then 5 else if i=1 then 1 else if i=2 then 6 else 7

def adderAction (a : Fin 9 → Sym) (r : Fin 3 → Sym × Move) : Fin 9 → Sym × Move :=
  fun i => if i=0 then r 0 else if i=2 then r 1 else if i=3 then r 2 else (a i,.stay)

def streamAction (a : Fin 9 → Sym) (r : Fin 4 → Sym × Move) : Fin 9 → Sym × Move :=
  fun i => if i=1 then r 1 else if i=5 then r 0 else if i=6 then r 2
    else if i=7 then r 3 else (a i,.stay)

def relayRaw (q : Relay) (a : Fin 9 → Sym) : State × (Fin 9 → Sym × Move) :=
  match q with
  | .seekSumEnd =>
      if a 2=.zero ∨ a 2=.one then
        (relayState .seekSumEnd,fun i => (a i,if i=2 then .right else .stay))
      else (relayState .copySum,fun i => (a i,if i=2 then .left else if i=5 then .right else .stay))
  | .copySum =>
      if a 2=.zero ∨ a 2=.one then
        (relayState .copySum,fun i => (if i=5 then a 2 else a i,
          if i=2 then .left else if i=5 then .right else .stay))
      else (relayState .copyDescriptor,fun i => (if i=5 then .sep else a i,
        if i=4 ∨ i=5 then .right else .stay))
  | .copyDescriptor =>
      if a 4=.zero ∨ a 4=.one then
        (relayState .copyDescriptor,fun i => (if i=5 then a 4 else a i,
          if i=4 ∨ i=5 then .right else .stay))
      else (relayState .rewind,fun i => (a i,if i=5 then .left else .stay))
  | .rewind =>
      if a 5=.start then (none,fun i => (a i,.stay))
      else (relayState .rewind,fun i => (a i,if i=5 then .left else .stay))
  | .openCarry => (relayState .copyCarry,fun i => (a i,if i=8 then .right else .stay))
  | .copyCarry =>
      if a 5=.zero ∨ a 5=.one then
        (relayState .copyCarry,fun i => (if i=8 then a 5 else a i,
          if i=5 ∨ i=8 then .right else .stay))
      else (none,fun i => (a i,.stay))

def rawTransition (q : State) (a : Fin 9 → Sym) : State × (Fin 9 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := TapeAdder.machine.δ q (fun i => a (adderTape i))
      (adderState r.1,adderAction a r.2)
  | some (.inr (.inl q)) => relayRaw q a
  | some (.inr (.inr q)) =>
      let r := CountedStream.machine.δ q (fun i => a (streamTape i))
      (streamState r.1,streamAction a r.2)

def transition (q : State) (a : Fin 9 → Sym) : State × (Fin 9 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem safe_input (s : Sym) (d : Move) : (safeStep s s d).1=s := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem raw_input (q : State) (a : Fin 9 → Sym) :
    ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl q =>
      simpa [rawTransition,adderAction,adderTape,MultitapeTM.inTape] using
        TapeAdder.machine.input_readonly q (fun i => a (adderTape i))
    | inr s =>
      cases s with
      | inr q => rfl
      | inl q =>
        cases q <;> simp only [rawTransition,relayRaw]
        all_goals try split_ifs
        all_goals simp

abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := some (.inl .start)
  qHalt := none
  start_ne_halt := by decide
  k := 9
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1=.start ∧ (safeStep (a i) _ _).2≠Move.left
    simp only [safeStep,hi,if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1≠.start
    simp only [safeStep,if_neg hi]
    split <;> simp_all
  halt_fixed := by intro a; simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1=a 0
    rw [raw_input]
    exact safe_input _ _

inductive Phase
  | add | transfer | prefix | carry
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.add,.transfer,.prefix,.carry}
  complete := by intro q; cases q <;> simp

def dispatch (phase : Phase) (_a : Fin 9 → Sym) : Option (Phase × State) :=
  match phase with
  | .add => some (.transfer,relayState .seekSumEnd)
  | .transfer => some (.prefix,streamState .start)
  | .prefix => some (.carry,relayState .openCarry)
  | .carry => none

noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Phase .add dispatch

def sumWord (x y : List Bool) : List Bool := bin (x.length+1) (val x+val y)

def blockSize (z : List Bool) : ℕ := val z+1

def digitWord (x y z : List Bool) : List Bool := (sumWord x y).reverse.take (blockSize z)

def carryWord (x y z : List Bool) : List Bool := (sumWord x y).reverse.drop (blockSize z)

/-- Incoming local arithmetic frame. A caller has already physically written
the descriptor bank; that preparation is not asserted to be free. -/
noncomputable def initialFrame (x y z : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=4 then machine.tapeOf (z.map machine.bitSym) else machine.tapeOf []
  head := fun _ => 0

/-- Both digit and next carry are emitted little-endian. Every bank and final
head is specified, including both restored countdown templates. -/
noncomputable def finalFrame (x y z : List Bool) : machine.Cfg where
  state := none
  cells := fun i =>
    if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=1 then machine.tapeOf ((digitWord x y z).map machine.bitSym)
    else if i=2 then machine.tapeOf ((sumWord x y).map machine.bitSym)
    else if i=3 then machine.tapeOf (x.map machine.bitSym)
    else if i=4 then machine.tapeOf (z.map machine.bitSym)
    else if i=5 then machine.tapeOf ((sumWord x y).reverse.map machine.bitSym++Sym.sep::z.map machine.bitSym)
    else if i=8 then machine.tapeOf ((carryWord x y z).map machine.bitSym)
    else machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep]))
  head := fun i =>
    if i=0 then x.length+1 else if i=1 then blockSize z+1
    else if i=2 ∨ i=3 then 0 else if i=5 then x.length+2
    else if i=8 then x.length+2-blockSize z else z.length+1

end IntMul.CarryStep


