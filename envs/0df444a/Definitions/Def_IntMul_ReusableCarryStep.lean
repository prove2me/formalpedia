-- Prove2me | Definitions.Def_IntMul_ReusableCarryStep
-- name    : IntMul_ReusableCarryStep
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T12:05:51.638037+00:00
-- url     : https://prove2.me/theorems/e5f26b71-55cb-44d5-a0b7-3c7481a0eccd
-- title:
--   Reusable physical streaming carry update with finite bank cleanup and carry return
-- statement:
--   One fixed fifteen-tape machine performs the streaming coefficient/carry update, physically erases the old saved carry, returns the canonical new carry to bank 12, physically erases all nine temporary arithmetic banks, and rewinds the retained B descriptor. A fixed finite caller schedules thirteen paid returns using a ten-element static eraser-bank tag set. It preserves the read-only root input, advanced input/output cursors and both restored width templates. The resulting workspace is ready for another coefficient. Prepared caller data and cursors remain explicit obligations. Correctness and full transition bounds are separate proof obligations.
-- source:
--   Original reusable physical coefficient/carry machine, using finite static eraser tags and actual seek, copy, rewind, erase and caller transitions. Written by Codex.

import Definitions.Def_IntMul_StreamCarryStep
import Definitions.Def_IntMul_TapeBankErase

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep)

/-- Static bank tags: old carry first, then the nine disposable work banks. -/
def eraseBank (i : Fin 10) : Fin 15 :=
  if i=0 then 12 else if i=1 then 2 else if i=2 then 3
  else if i=3 then 4 else if i=4 then 5 else if i=5 then 7
  else if i=6 then 8 else if i=7 then 9 else if i=8 then 10 else 11

theorem eraseBank_writable (i : Fin 10) : 1 ≤ (eraseBank i).val := by
  fin_cases i <;> decide

inductive Relay
  | seekCarry | copyCarry | rewindCarry | seekDescriptor
  deriving DecidableEq

instance : Fintype Relay where
  elems := {.seekCarry,.copyCarry,.rewindCarry,.seekDescriptor}
  complete := by intro q;cases q <;> simp

abbrev State := Option (StreamCarryStep.machine.K ⊕ ((Fin 10 × TapeBankErase.State) ⊕ Relay))

noncomputable def calcState (q : StreamCarryStep.machine.K) : State :=
  if q=none then none else some (.inl q)

def eraseState (i : Fin 10) (q : TapeBankErase.State) : State :=
  if q=.halt then none else some (.inr (.inl (i,q)))

def relayState (q : Relay) : State := some (.inr (.inr q))

def relayRaw (q : Relay) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | .seekCarry =>
      if a 11=.start then
        (relayState .copyCarry,fun i => (a i,if i=11 ∨ i=12 then .right else .stay))
      else (relayState .seekCarry,fun i => (a i,if i=11 then .left else .stay))
  | .copyCarry =>
      if a 11=.zero ∨ a 11=.one then
        (relayState .copyCarry,fun i => (if i=12 then a 11 else a i,
          if i=11 ∨ i=12 then .right else .stay))
      else (relayState .rewindCarry,fun i => (a i,if i=11 ∨ i=12 then .left else .stay))
  | .rewindCarry =>
      if a 12=.start then (none,fun i => (a i,.stay))
      else (relayState .rewindCarry,fun i => (a i,if i=11 ∨ i=12 then .left else .stay))
  | .seekDescriptor =>
      if a 6=.start then (none,fun i => (a i,.stay))
      else (relayState .seekDescriptor,fun i => (a i,if i=6 then .left else .stay))

noncomputable def rawTransition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := StreamCarryStep.machine.δ q a
      (calcState r.1,r.2)
  | some (.inr (.inl (i,q))) =>
      let r := (TapeBankErase.machine 13 (eraseBank i) (eraseBank_writable i)).δ q a
      (eraseState i r.1,r.2)
  | some (.inr (.inr q)) => relayRaw q a

noncomputable def transition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input (q : State) (a : Fin 15 → Sym) :
    ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl q => exact StreamCarryStep.machine.input_readonly q a
    | inr s =>
      cases s with
      | inl iq => exact (TapeBankErase.machine 13 (eraseBank iq.1) (eraseBank_writable iq.1)).input_readonly iq.2 a
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
  qStart := calcState StreamCarryStep.machine.qStart
  qHalt := none
  start_ne_halt := by
    simp only [calcState]
    rw [if_neg StreamCarryStep.machine.start_ne_halt]
    exact Option.some_ne_none _
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
    change (safeStep (a 0) ((rawTransition q a).2 0).1 _).1=a 0
    rw [raw_input]
    by_cases h : a 0=Sym.start <;> simp [safeStep,h]

inductive Phase
  | calc | erase (i : Fin 10) | returnCarry | descriptor
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.calc,.returnCarry,.descriptor} ∪ Finset.univ.image .erase
  complete := by intro q;cases q <;> simp

noncomputable def dispatch (phase : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match phase with
  | .calc => some (.erase 0,eraseState 0 .rewind)
  | .erase i =>
      if i=0 then some (.returnCarry,relayState .seekCarry)
      else if h : i.val < 9 then
        let j : Fin 10 := ⟨i.val+1,by omega⟩
        some (.erase j,eraseState j .rewind)
      else some (.descriptor,relayState .seekDescriptor)
  | .returnCarry => some (.erase 1,eraseState 1 .rewind)
  | .descriptor => none

noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Phase .calc dispatch

/-- The earlier streaming frame, with the same fifteen physical tapes. -/
noncomputable def initialFrame (pre x tail a y z l : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := (StreamCarryStep.initialFrame pre x tail a y z l).cells
  head := (StreamCarryStep.initialFrame pre x tail a y z l).head

/-- Fresh workspace for the next coefficient. The new carry has been physically
returned to bank 12; nine arithmetic banks are physically erased. -/
noncomputable def finalFrame (pre x tail a y z l : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then StreamCarryStep.rootTape pre x tail l
    else if i=1 then machine.tapeOf ((a++CarryStep.digitWord x y z).map machine.bitSym)
    else if i=6 then machine.tapeOf (z.map machine.bitSym)
    else if i=12 then machine.tapeOf ((PaddedCarryStep.nextCarryWord x y z).map machine.bitSym)
    else if i=13 ∨ i=14 then StreamCarryStep.descriptorTape l else machine.tapeOf []
  head := fun i => if i=0 then pre.length+x.length+1
    else if i=1 then a.length+CarryStep.blockSize z+1
    else if i=13 ∨ i=14 then l.length+1 else 0

end IntMul.ReusableCarryStep


