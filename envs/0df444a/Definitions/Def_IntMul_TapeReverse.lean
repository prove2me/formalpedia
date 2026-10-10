-- Prove2me | Definitions.Def_IntMul_TapeReverse
-- name    : IntMul_TapeReverse
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T09:06:09.570968+00:00
-- url     : https://prove2.me/theorems/cedf3f1a-d691-4466-95f9-adf8dcb7170f
-- title:
--   Fixed two-tape binary word reversal machine
-- statement:
--   One fixed two-tape, five-symbol, four-state multitape Turing machine scans the first binary operand to the delimiter, then traverses it backwards while writing bits forwards on output. The original input is read-only. Defines complete seek and reverse-copy boundary configurations. No numerical length, coordinate or reversal oracle is supplied to the finite transition table. Correctness and exact execution clock are separate theorem obligations.
-- source:
--   Original actual word-reversal routine in the campaign MultitapeTM model. Written by Codex.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.TapeReverse

open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive State
  | start | seek | copy | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start,.seek,.copy,.halt}
  complete := by intro q; cases q <;> simp

def rawTransition (q : State) (a : Fin 2 → Sym) : State × (Fin 2 → Sym × Move) :=
  match q with
  | .start => (.seek,fun i => (a i,if i=0 then .right else .stay))
  | .seek =>
      if a 0=.zero ∨ a 0=.one then
        (.seek,fun i => (a i,if i=0 then .right else .stay))
      else if a 0=.sep then
        (.copy,fun i => (a i,if i=0 then .left else .right))
      else (.halt,fun i => (a i,.stay))
  | .copy =>
      if a 0=.zero ∨ a 0=.one then
        (.copy,fun i => (if i=0 then a i else a 0,if i=0 then .left else .right))
      else (.halt,fun i => (a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 2 → Sym) : State × (Fin 2 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem safe_input (s : Sym) (d : Move) : (safeStep s s d).1=s := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .start
  qHalt := .halt
  start_ne_halt := by decide
  k := 2
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
  halt_fixed := by
    intro a
    simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    have h : ((rawTransition q a).2 0).1=a 0 := by
      cases q <;> simp only [rawTransition]
      all_goals try split_ifs
      all_goals simp
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1=a 0
    rw [h]
    exact safe_input _ _

def seekFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .seek
  cells := fun i => if i=0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i=0 then j+1 else 0

/-- Exact reverse-copy boundary: j input bits remain to the left, while the
reversed suffix is already present on output. -/
def frame (x y : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i=0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else machine.tapeOf ((x.drop j).reverse.map machine.bitSym)
  head := fun i => if i=0 then j else x.length-j+1

end IntMul.TapeReverse


