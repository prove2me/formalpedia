-- Prove2me | Definitions.Def_IntMul_FixedOutputWidth
-- name    : IntMul_FixedOutputWidth
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T13:25:48.168456+00:00
-- url     : https://prove2.me/theorems/0c5e1998-9152-4d93-bab4-a9a2329e26fc
-- title:
--   Real fixed-width output return with charged counted prefix, copies and erasures
-- statement:
--   A fixed fifteen-tape machine converts a binary output word $w$ to its desired low-order width $W=\operatorname{val}(d)+1$. The desired width is physically present only through two explicitly prepared binary counter/template banks. The machine reverses the original word, seeks its real marker, reads a counted low-bit prefix, erases the original output, copies the prefix back in big-endian order, clears scratch and globally halts. Every other caller tape and head is retained and both counter/templates are restored. No input-length or head oracle is supplied to the transition table. Correctness, exact terminal frames and the linear physical clock are separate theorem obligations. Incoming descriptor preparation remains explicit caller work.
-- source:
--   Original complete physical exact output-width return on the existing fifteen-tape alphabet, with six paid finite caller phases. Written by Codex.

import Definitions.Def_IntMul_CanonicalOutput
import Definitions.Def_IntMul_PrefixRead

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive Relay | seek | turn | reverse deriving DecidableEq
instance : Fintype Relay where
  elems := {.seek,.turn,.reverse}
  complete := by intro q;cases q <;> simp

abbrev State := Option (CanonicalOutput.machine.K ⊕
  (CountedStream.State ⊕ ((Fin 2 × TapeBankErase.State) ⊕ Relay)))

noncomputable def canonicalState (q : CanonicalOutput.machine.K) : State :=
  if q=none then none else some (.inl q)
def readState (q : CountedStream.State) : State :=
  if q=.halt then none else some (.inr (.inl q))
def eraseBank (i : Fin 2) : Fin 15 := if i=0 then 1 else 2
theorem eraseBank_writable (i : Fin 2) : 1 ≤ (eraseBank i).val := by fin_cases i <;> decide
def eraseState (i : Fin 2) (q : TapeBankErase.State) : State :=
  if q=.halt then none else some (.inr (.inr (.inl (i,q))))
def relayState (q : Relay) : State := some (.inr (.inr (.inr q)))

def readTape (i : Fin 4) : Fin 15 :=
  if i=0 then 1 else if i=1 then 2 else if i=2 then 3 else 4
def readAction (a : Fin 15 → Sym) (r : Fin 4 → Sym × Move) : Fin 15 → Sym × Move :=
  fun i => if i=1 then r 0 else if i=2 then r 1 else if i=3 then r 2
    else if i=4 then r 3 else (a i,.stay)

def relayRaw (q : Relay) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | .seek =>
      if a 1=.start then
        (none,fun i => (a i,if i=1 ∨ i=2 then .right else .stay))
      else (relayState .seek,fun i => (a i,if i=1 then .left else .stay))
  | .turn =>
      (relayState .reverse,fun i => (a i,if i=2 then .left else if i=1 then .right else .stay))
  | .reverse =>
      if a 2=.zero ∨ a 2=.one then
        (relayState .reverse,fun i => (if i=1 then a 2 else a i,
          if i=2 then .left else if i=1 then .right else .stay))
      else (none,fun i => (a i,.stay))

noncomputable def rawTransition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CanonicalOutput.machine.δ q a
      (canonicalState r.1,r.2)
  | some (.inr (.inl q)) =>
      let r := CountedStream.machine.δ q (fun i => a (readTape i))
      (readState r.1,readAction a r.2)
  | some (.inr (.inr (.inl (i,q)))) =>
      let r := (TapeBankErase.machine 13 (eraseBank i) (eraseBank_writable i)).δ q a
      (eraseState i r.1,r.2)
  | some (.inr (.inr (.inr q))) => relayRaw q a

noncomputable def transition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input (q : State) (a : Fin 15 → Sym) : ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
      cases s with
      | inl q => exact CanonicalOutput.machine.input_readonly q a
      | inr s =>
          cases s with
          | inl q => rfl
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
  qStart := canonicalState CanonicalOutput.machine.qStart
  qHalt := none
  start_ne_halt := by simp only [canonicalState,CanonicalOutput.machine,FiniteCaller.machine,reduceCtorEq,if_false];exact Option.some_ne_none _
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

inductive Phase | canonical | seek | read | eraseOutput | reverse | eraseScratch deriving DecidableEq
instance : Fintype Phase where
  elems := {.canonical,.seek,.read,.eraseOutput,.reverse,.eraseScratch}
  complete := by intro q;cases q <;> simp

noncomputable def dispatch (q : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match q with
  | .canonical => some (.seek,relayState .seek)
  | .seek => some (.read,readState .emit)
  | .read => some (.eraseOutput,eraseState 0 .rewind)
  | .eraseOutput => some (.reverse,relayState .turn)
  | .reverse => some (.eraseScratch,eraseState 1 .rewind)
  | .eraseScratch => none

noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .canonical dispatch

def width (d : List Bool) : ℕ := val d+1
def outputWord (w d : List Bool) : List Bool := (w.reverse.take (width d)).reverse

noncomputable def descriptorTape (d : List Bool) : ℕ → Sym := subroutine.tapeOf (Sym.sep::(d.map subroutine.bitSym++[Sym.sep]))

/-- Desired width is physically supplied only through prepared counter/template
banks 3/4. Every other caller bank/head is retained. No descriptor loading,
input-derived length, or global initialization is asserted to be free. -/
noncomputable def initialFrame (base : machine.Cfg) (w d : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := Function.update (Function.update (Function.update (Function.update base.cells
    1 (machine.tapeOf (w.map machine.bitSym))) 2 (machine.tapeOf [])) 3 (descriptorTape d)) 4 (descriptorTape d)
  head := Function.update (Function.update (Function.update (Function.update base.head
    1 (w.length+1)) 2 0) 3 (d.length+1)) 4 (d.length+1)

noncomputable def finalFrame (base : machine.Cfg) (w d : List Bool) : machine.Cfg where
  state := none
  cells := Function.update (Function.update (Function.update (Function.update base.cells
    1 (machine.tapeOf ((outputWord w d).map machine.bitSym))) 2 (machine.tapeOf [])) 3 (descriptorTape d)) 4 (descriptorTape d)
  head := Function.update (Function.update (Function.update (Function.update base.head
    1 (width d+1)) 2 0) 3 (d.length+1)) 4 (d.length+1)

end IntMul.FixedOutputWidth


