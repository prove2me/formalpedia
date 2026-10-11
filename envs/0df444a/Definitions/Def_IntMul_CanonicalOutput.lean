-- Prove2me | Definitions.Def_IntMul_CanonicalOutput
-- name    : IntMul_CanonicalOutput
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T12:50:23.941578+00:00
-- url     : https://prove2.me/theorems/87116e06-835d-4d64-a662-6b5b0de2264c
-- title:
--   Physical reversal of completed output with retained caller frame and cleared scratch
-- statement:
--   A fixed fifteen-tape machine physically reverses the completed finite binary output word on bank 1, using bank 2 as scratch. It turns and copies backwards into scratch, erases the original output, seeks the actual scratch marker, copies forwards to output and erases scratch. Every other caller tape and head is retained. The output and scratch frames, four charged caller phases, and exact global halt are explicit. The table has no length or head oracle. Correctness and the linear physical transition bound are separate theorem obligations.
-- source:
--   Original complete physical output order repair, including both finite erasures and paid finite caller returns. Written by Codex.

import Definitions.Def_IntMul_TapeBankErase
import Definitions.Def_IntMul_FiniteCaller

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CanonicalOutput
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive Relay
  | turn | reverse | seek | copy
  deriving DecidableEq

instance : Fintype Relay where
  elems := {.turn,.reverse,.seek,.copy}
  complete := by intro q;cases q <;> simp

abbrev State := Option ((Fin 2 × TapeBankErase.State) ⊕ Relay)

def eraseBank (i : Fin 2) : Fin 15 := if i=0 then 1 else 2

theorem eraseBank_writable (i : Fin 2) : 1 ≤ (eraseBank i).val := by fin_cases i <;> decide

def eraseState (i : Fin 2) (q : TapeBankErase.State) : State :=
  if q=.halt then none else some (.inl (i,q))

def relayState (q : Relay) : State := some (.inr q)

def relayRaw (q : Relay) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | .turn => (relayState .reverse,fun i => (a i,if i=1 then .left else if i=2 then .right else .stay))
  | .reverse =>
      if a 1=.zero ∨ a 1=.one then
        (relayState .reverse,fun i => (if i=2 then a 1 else a i,
          if i=1 then .left else if i=2 then .right else .stay))
      else (none,fun i => (a i,.stay))
  | .seek =>
      if a 2=.start then
        (relayState .copy,fun i => (a i,if i=1 ∨ i=2 then .right else .stay))
      else (relayState .seek,fun i => (a i,if i=2 then .left else .stay))
  | .copy =>
      if a 2=.zero ∨ a 2=.one then
        (relayState .copy,fun i => (if i=1 then a 2 else a i,
          if i=1 ∨ i=2 then .right else .stay))
      else (none,fun i => (a i,.stay))

def rawTransition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl (i,q)) =>
      let r := (TapeBankErase.machine 13 (eraseBank i) (eraseBank_writable i)).δ q a
      (eraseState i r.1,r.2)
  | some (.inr q) => relayRaw q a

def transition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input (q : State) (a : Fin 15 → Sym) : ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl iq => exact (TapeBankErase.machine 13 (eraseBank iq.1) (eraseBank_writable iq.1)).input_readonly iq.2 a
    | inr q =>
      cases q <;> simp only [rawTransition,relayRaw]
      all_goals try split_ifs
      all_goals simp_all

abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := relayState .turn
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
    change (safeStep (a 0) ((rawTransition q a).2 0).1 _).1=a 0
    rw [raw_input]
    by_cases h : a 0=Sym.start <;> simp [safeStep,h]

inductive Phase
  | reverse | eraseOutput | copy | eraseScratch
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.reverse,.eraseOutput,.copy,.eraseScratch}
  complete := by intro q;cases q <;> simp

def dispatch (q : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match q with
  | .reverse => some (.eraseOutput,eraseState 0 .rewind)
  | .eraseOutput => some (.copy,relayState .seek)
  | .copy => some (.eraseScratch,eraseState 1 .rewind)
  | .eraseScratch => none

noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .reverse dispatch

/-- Output 1 contains the finite little-endian word at its retained end cursor;
scratch 2 is empty. Every other real caller bank and head is arbitrary retained
frame data. All marker/open/copy/erase/return transitions are paid separately. -/
noncomputable def initialFrame (base : machine.Cfg) (w : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := Function.update (Function.update base.cells 1 (machine.tapeOf (w.map machine.bitSym))) 2 (machine.tapeOf [])
  head := Function.update (Function.update base.head 1 (w.length+1)) 2 0

/-- Canonical reversed output, end cursor retained, scratch physically empty
with head zero, every other caller cell/head unchanged, and global halt. -/
noncomputable def finalFrame (base : machine.Cfg) (w : List Bool) : machine.Cfg where
  state := none
  cells := Function.update (Function.update base.cells 1 (machine.tapeOf (w.reverse.map machine.bitSym))) 2 (machine.tapeOf [])
  head := Function.update (Function.update base.head 1 (w.length+1)) 2 0

end IntMul.CanonicalOutput


