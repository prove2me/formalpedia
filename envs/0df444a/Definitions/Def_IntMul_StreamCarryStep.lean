-- Prove2me | Definitions.Def_IntMul_StreamCarryStep
-- name    : IntMul_StreamCarryStep
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T10:54:51.690587+00:00
-- url     : https://prove2.me/theorems/e57064ec-77e6-4a11-a6e3-1e676f41b2bb
-- title:
--   Fixed fifteen-tape streaming coefficient carry-update machine
-- statement:
--   One actual finite fifteen-tape machine opens a scratch request, reads one interior coefficient through the existing countdown, writes a literal delimiter and copies the retained previous carry, rewinds the request, runs canonical padded-carry arithmetic on fixed physical banks, and appends the low digit to the global output. It freezes the root input during arithmetic and preserves its advanced cursor and the width templates. All incoming descriptor, previous-carry and cursor preparation is explicit in the caller frame. The finite table reads only state and scanned symbols. Correctness and complete actual clock bounds are separate obligations.
-- source:
--   Original complete physical streaming carry-update machine in the integer multiplication multitape model. Written by Codex.

import Definitions.Def_IntMul_PaddedCarryStep
import Definitions.Def_IntMul_FramedBlockRead

namespace IntMul.StreamCarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive Relay
  | openRead | openCarry | copyCarry | rewindRequest | seekDigitStart | copyDigit
  deriving DecidableEq

instance : Fintype Relay where
  elems := {.openRead,.openCarry,.copyCarry,.rewindRequest,.seekDigitStart,.copyDigit}
  complete := by intro q;cases q <;> simp

abbrev State := Option (CountedStream.State ⊕ (PaddedCarryStep.machine.K ⊕ Relay))

def readState (q : CountedStream.State) : State :=
  if q=.halt then none else some (.inl q)

noncomputable def mainState (q : PaddedCarryStep.machine.K) : State :=
  if q=none then none else some (.inr (.inl q))

def relayState (q : Relay) : State := some (.inr (.inr q))

def readTape (i : Fin 4) : Fin 15 :=
  if i=0 then 0 else if i=1 then 2 else if i=2 then 13 else 14

def mainTape (i : Fin 10) : Fin 15 := ⟨i.val+2,by omega⟩

def readAction (a : Fin 15 → Sym) (r : Fin 4 → Sym × Move) : Fin 15 → Sym × Move :=
  fun i => if i=0 then r 0 else if i=2 then r 1 else if i=13 then r 2
    else if i=14 then r 3 else (a i,.stay)

def mainAction (a : Fin 15 → Sym) (r : Fin 10 → Sym × Move) : Fin 15 → Sym × Move :=
  fun i => if h : 2 ≤ i.val ∧ i.val < 12 then r ⟨i.val-2,by change i.val-2 < 10; omega⟩ else (a i,.stay)

def relayRaw (q : Relay) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | .openRead => (readState .emit,fun i => (a i,if i=2 then .right else .stay))
  | .openCarry => (relayState .copyCarry,fun i => (if i=2 then .sep else a i,
      if i=2 ∨ i=12 then .right else .stay))
  | .copyCarry =>
      if a 12=.zero ∨ a 12=.one then
        (relayState .copyCarry,fun i => (if i=2 then a 12 else a i,
          if i=2 ∨ i=12 then .right else .stay))
      else (relayState .rewindRequest,fun i => (a i,if i=2 then .left else .stay))
  | .rewindRequest =>
      if a 2=.start then (none,fun i => (a i,.stay))
      else (relayState .rewindRequest,fun i => (a i,if i=2 then .left else .stay))
  | .seekDigitStart =>
      if a 3=.start then (relayState .copyDigit,fun i => (a i,if i=3 then .right else .stay))
      else (relayState .seekDigitStart,fun i => (a i,if i=3 then .left else .stay))
  | .copyDigit =>
      if a 3=.zero ∨ a 3=.one then
        (relayState .copyDigit,fun i => (if i=1 then a 3 else a i,
          if i=1 ∨ i=3 then .right else .stay))
      else (none,fun i => (a i,.stay))

noncomputable def rawTransition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CountedStream.machine.δ q (fun i => a (readTape i))
      (readState r.1,readAction a r.2)
  | some (.inr (.inl q)) =>
      let r := PaddedCarryStep.machine.δ q (fun i => a (mainTape i))
      (mainState r.1,mainAction a r.2)
  | some (.inr (.inr q)) => relayRaw q a

noncomputable def transition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem safe_input (s : Sym) (d : Move) : (safeStep s s d).1=s := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem raw_input (q : State) (a : Fin 15 → Sym) :
    ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl q =>
      simpa [rawTransition,readAction,readTape,MultitapeTM.inTape] using
        CountedStream.machine.input_readonly q (fun i => a (readTape i))
    | inr s =>
      cases s with
      | inl q => rfl
      | inr q =>
        cases q <;> simp only [rawTransition,relayRaw]
        all_goals try split_ifs
        all_goals simp_all

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := relayState .openRead
  qHalt := none
  start_ne_halt := by decide
  k := 15
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
  halt_fixed := by intro a;simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1=a 0
    rw [raw_input]
    exact safe_input _ _

inductive Phase
  | read | prepare | arithmetic | output
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.read,.prepare,.arithmetic,.output}
  complete := by intro q;cases q <;> simp

noncomputable def dispatch (phase : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match phase with
  | .read => some (.prepare,relayState .openCarry)
  | .prepare => some (.arithmetic,mainState PaddedCarryStep.machine.qStart)
  | .arithmetic => some (.output,relayState .seekDigitStart)
  | .output => none

noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Phase .read dispatch

noncomputable def rootTape (pre x tail l : List Bool) : ℕ → Sym :=
  machine.tapeOf ((pre++x++tail).map machine.bitSym++Sym.sep::l.map machine.bitSym)

noncomputable def descriptorTape (l : List Bool) : ℕ → Sym :=
  machine.tapeOf (Sym.sep::(l.map machine.bitSym++[Sym.sep]))

/-- Prepared incoming caller frame, retaining an interior coefficient cursor,
output prefix, previous canonical carry and both width templates. Loading or
positioning these data is an explicit earlier caller obligation. -/
noncomputable def initialFrame (pre x tail a y z l : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := fun i => if i=0 then rootTape pre x tail l
    else if i=1 then machine.tapeOf (a.map machine.bitSym)
    else if i=6 then machine.tapeOf (z.map machine.bitSym)
    else if i=12 then machine.tapeOf (y.map machine.bitSym)
    else if i=13 ∨ i=14 then descriptorTape l else machine.tapeOf []
  head := fun i => if i=0 then pre.length+1 else if i=1 then a.length+1
    else if i=13 ∨ i=14 then l.length+1 else 0

/-- Complete terminal frame: coefficient cursor advanced, low digit appended,
new canonical carry on bank 11, and all arithmetic and width banks explicit. -/
noncomputable def finalFrame (pre x tail a y z l : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then rootTape pre x tail l
    else if i=1 then machine.tapeOf ((a++CarryStep.digitWord x y z).map machine.bitSym)
    else if h : 2 ≤ i.val ∧ i.val < 12 then
      (PaddedCarryStep.finalFrame x y z).cells ⟨i.val-2,by change i.val-2 < 10; omega⟩
    else if i=12 then machine.tapeOf (y.map machine.bitSym) else descriptorTape l
  head := fun i => if i=0 then pre.length+x.length+1
    else if i=1 then a.length+CarryStep.blockSize z+1
    else if h : 2 ≤ i.val ∧ i.val < 12 then
      (PaddedCarryStep.finalFrame x y z).head ⟨i.val-2,by change i.val-2 < 10; omega⟩
    else if i=12 then x.length+1 else l.length+1

end IntMul.StreamCarryStep


