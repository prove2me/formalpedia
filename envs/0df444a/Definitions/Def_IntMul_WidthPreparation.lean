-- Prove2me | Definitions.Def_IntMul_WidthPreparation
-- name    : IntMul_WidthPreparation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T13:37:42.961348+00:00
-- url     : https://prove2.me/theorems/db25f8ea-c222-484f-9c56-f29b68fd8de6
-- title:
--   Actual retained-width descriptor preparation with two counter banks and real rewind
-- statement:
--   One fixed sixteen-tape, five-symbol machine physically copies a retained binary width descriptor from bank 15 to empty counter/template banks 3 and 4, writes both real separator delimiters, places both counter heads at their least-significant-bit cursors, rewinds the retained descriptor to its real start marker and halts. Every other caller tape and head is retained. Incoming descriptor presence and empty counter banks are explicit caller obligations. Correctness, the exact complete terminal frame and its exact linear transition count are separate theorem obligations.
-- source:
--   Original actual descriptor preparation required between complete coefficient product recovery and fixed-width output conversion. Written by Codex.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.WidthPreparation
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive State | advance | open | copy | rewind | halt deriving DecidableEq
instance : Fintype State where
  elems := {.advance,.open,.copy,.rewind,.halt}
  complete := by intro q;cases q <;> simp

def rawTransition (q : State) (a : Fin 16 → Sym) : State × (Fin 16 → Sym × Move) :=
  match q with
  | .advance => (.open,fun i => (a i,if i=3 ∨ i=4 ∨ i=15 then .right else .stay))
  | .open => (.copy,fun i => (if i=3 ∨ i=4 then .sep else a i,if i=3 ∨ i=4 then .right else .stay))
  | .copy =>
      if a 15=.zero ∨ a 15=.one then
        (.copy,fun i => (if i=3 ∨ i=4 then a 15 else a i,
          if i=3 ∨ i=4 ∨ i=15 then .right else .stay))
      else (.rewind,fun i => (if i=3 ∨ i=4 then .sep else a i,
        if i=3 ∨ i=4 ∨ i=15 then .left else .stay))
  | .rewind =>
      if a 15=.start then (.halt,fun i => (a i,.stay))
      else (.rewind,fun i => (a i,if i=15 then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 16 → Sym) : State × (Fin 16 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input (q : State) (a : Fin 16 → Sym) : ((rawTransition q a).2 0).1=a 0 := by
  cases q <;> simp only [rawTransition]
  all_goals try split_ifs
  all_goals simp_all

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .advance
  qHalt := .halt
  start_ne_halt := by decide
  k := 16
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

def descriptorTape (d : List Bool) : ℕ → Sym := machine.tapeOf (Sym.sep::(d.map machine.bitSym++[Sym.sep]))

/-- Retained width word on bank 15; two genuinely empty destination banks.
All input, output and other caller cells/heads are retained. -/
def initialFrame (base : machine.Cfg) (d : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := Function.update (Function.update (Function.update base.cells 15 (machine.tapeOf (d.map machine.bitSym)))
    3 (machine.tapeOf [])) 4 (machine.tapeOf [])
  head := Function.update (Function.update (Function.update base.head 15 0) 3 0) 4 0

/-- Both actual countdown/template banks are physically prepared at their
least-significant-bit cursors; retained width word is rewound to its marker. -/
def finalFrame (base : machine.Cfg) (d : List Bool) : machine.Cfg where
  state := machine.qHalt
  cells := Function.update (Function.update (Function.update base.cells 15 (machine.tapeOf (d.map machine.bitSym)))
    3 (descriptorTape d)) 4 (descriptorTape d)
  head := Function.update (Function.update (Function.update base.head 15 0) 3 (d.length+1)) 4 (d.length+1)

end IntMul.WidthPreparation


