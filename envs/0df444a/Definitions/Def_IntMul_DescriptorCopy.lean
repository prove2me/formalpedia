-- Prove2me | Definitions.Def_IntMul_DescriptorCopy
-- name    : IntMul_DescriptorCopy
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T17:27:26.361024+00:00
-- url     : https://prove2.me/theorems/e0f5e77a-c092-48aa-8ba5-dbbff5b6db63
-- title:
--   Physical copying of a retained binary descriptor with both heads returned to their markers
-- statement:
--   A fixed three-tape finite routine starts from a framed binary word w on tape 1 at its actual marker and an empty destination tape 2 at its marker, retaining arbitrary original input cells and head. It copies the word bit by bit, detects its terminating blank and physically rewinds both source and destination heads to their actual markers. Source cells and all original input data are retained. Exact final-frame correctness and the transition clock are separate theorem obligations.
-- source:
--   Original complete physical retained-descriptor copying primitive. Written by Codex.

import Definitions.Def_IntMul_TapeAdder
namespace IntMul.DescriptorCopy
open TapeCopy (Sym)
inductive State | advance | copy | rewind | halt deriving DecidableEq
instance : Fintype State where
  elems := {.advance,.copy,.rewind,.halt}
  complete := by intro q;cases q <;> simp
def rawTransition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  match q with
  | .advance => (.copy,fun i => (a i,if i=1 ∨ i=2 then .right else .stay))
  | .copy => if a 1=.zero ∨ a 1=.one then
      (.copy,fun i => (if i=2 then a 1 else a i,if i=1 ∨ i=2 then .right else .stay))
    else (.rewind,fun i => (a i,if i=1 ∨ i=2 then .left else .stay))
  | .rewind => if a 1=.start then (.halt,fun i => (a i,.stay))
    else (.rewind,fun i => (a i,if i=1 ∨ i=2 then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))
def transition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => TapeAdder.safeStep (a i) (r.2 i).1 (r.2 i).2)
private theorem raw_input (q : State) (a : Fin 3 → Sym) : ((rawTransition q a).2 0).1=a 0 := by
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
  k := 3
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (TapeAdder.safeStep (a i) _ _).1=Sym.start ∧ (TapeAdder.safeStep (a i) _ _).2≠Move.left
    simp only [TapeAdder.safeStep,hi,if_true];split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    change (TapeAdder.safeStep (a i) _ _).1≠Sym.start
    simp only [TapeAdder.safeStep,if_neg hi];split <;> simp_all
  halt_fixed := by intro a;simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (TapeAdder.safeStep (a 0) ((rawTransition q a).2 0).1 _).1=a 0
    rw [raw_input]
    by_cases h : a 0=Sym.start <;> simp [TapeAdder.safeStep,h]
def initialFrame (base : machine.Cfg) (w : List Bool) : machine.Cfg where
  state := .advance
  cells := Function.update (Function.update base.cells 1 (machine.tapeOf (w.map machine.bitSym))) 2 (machine.tapeOf [])
  head := Function.update (Function.update base.head 1 0) 2 0
def copyFrame (base : machine.Cfg) (w : List Bool) (j : ℕ) : machine.Cfg where
  state := .copy
  cells := Function.update (Function.update base.cells 1 (machine.tapeOf (w.map machine.bitSym))) 2
    (machine.tapeOf ((w.take j).map machine.bitSym))
  head := Function.update (Function.update base.head 1 (j+1)) 2 (j+1)
def rewindFrame (base : machine.Cfg) (w : List Bool) (p : ℕ) : machine.Cfg where
  state := .rewind
  cells := Function.update (Function.update base.cells 1 (machine.tapeOf (w.map machine.bitSym))) 2
    (machine.tapeOf (w.map machine.bitSym))
  head := Function.update (Function.update base.head 1 p) 2 p
def finalFrame (base : machine.Cfg) (w : List Bool) : machine.Cfg :=
  {rewindFrame base w 0 with state := .halt}
end IntMul.DescriptorCopy


