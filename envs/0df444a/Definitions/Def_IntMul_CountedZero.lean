-- Prove2me | Definitions.Def_IntMul_CountedZero
-- name    : IntMul_CountedZero
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:27:18.133591+00:00
-- url     : https://prove2.me/theorems/9485e863-3ac7-41aa-beac-25b5e3309fda
-- title:
--   Physical binary-counted zero word initialization without a supplied zero payload
-- statement:
--   A fixed four-tape finite machine opens an initially empty output bank, emits one actual zero bit per countdown cycle, restores its two prepared binary countdown/template banks and halts. The descriptor $l$ represents $N-1$, so the intended output is the $N$-bit zero word. Original input cells and head are retained; no zero payload is supplied. Preparing the descriptor templates is an explicit incoming obligation. Correctness, the exact final configuration and the linear actual transition clock are separate theorem obligations.
-- source:
--   Original physical initial-carry zero word generator using the actual binary decrement and template reset table. Written by Codex.

import Definitions.Def_IntMul_CountedStream
namespace IntMul.CountedZero
open TapeCopy (Sym)
open TapeAdder (safeStep encode decode)
open CountedStream
abbrev State := CountedStream.State
def rawTransition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i, .stay))
  | .start => (.emit,fun i => (a i,if i=1 then .right else .stay))
  | .scanX =>
      if a 0 = .zero ∨ a 0 = .one then
        (.scanX, fun i => (a i, if i = 0 then .right else .stay))
      else (.copyY, fun i =>
        (if i = 2 ∨ i = 3 then .sep else a i,
          if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay))
  | .copyY =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copyY, fun i => (if i = 2 ∨ i = 3 then a 0 else a i,
          if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay))
      else (.rewindInput, fun i =>
        (if i = 2 ∨ i = 3 then .sep else a i,
          if i = 0 ∨ i = 2 ∨ i = 3 then .left else .stay))
  | .rewindInput =>
      if a 0 = .start then (.emit, fun i => (a i, if i = 0 then .right else .stay))
      else (.rewindInput, fun i => (a i, if i = 0 then .left else .stay))
  | .emit => (.carry,fun i => (if i=1 then .zero else a i,
      if i=1 then .right else .stay))
  | .carry =>
      if a 2 = .zero then
        (.carry, fun i => (if i = 2 then .one else a i, if i = 2 then .left else .stay))
      else if a 2 = .one then
        (.rewind false, fun i => (if i = 2 then .zero else a i, if i = 2 then .right else .stay))
      else if a 2 = .sep then
        (.rewind true, fun i => (a i, if i = 2 then .right else .stay))
      else (.halt, fun i => (a i, .stay))
  | .rewind f =>
      if a 2 = .zero ∨ a 2 = .one then
        (.rewind f, fun i => (a i, if i = 2 then .right else .stay))
      else if a 2 = .sep then
        (.done f, fun i => (a i, if i = 2 then .left else .stay))
      else (.halt, fun i => (a i, .stay))
  | .done f => (if f then .resetLeft else .emit, fun i => (a i, .stay))
  | .resetLeft =>
      if a 2 = .zero ∨ a 2 = .one then
        (.resetLeft, fun i => (if i = 2 then a 3 else a i,
          if i = 2 ∨ i = 3 then .left else .stay))
      else if a 2 = .sep then
        (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay))
      else (.halt, fun i => (a i, .stay))
  | .resetRight =>
      if a 2 = .zero ∨ a 2 = .one then
        (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay))
      else if a 2 = .sep then
        (.halt, fun i => (a i, if i = 2 ∨ i = 3 then .left else .stay))
      else (.halt, fun i => (a i, .stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  let r := rawTransition q a
  (r.1, fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

theorem raw_input_readonly (q : State) (a : Fin 4 → Sym) :
    ((rawTransition q a).2 0).1 = a 0 := by
  cases q <;> simp [rawTransition]
  all_goals repeat' first | rfl | split

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
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1 = .start ∧ (safeStep (a i) _ _).2 ≠ .left
    rw [hi]
    simp only [safeStep, if_pos rfl]
    by_cases hd : ((rawTransition q a).2 i).2 = Move.left
    · simp [hd]
    · simp [hd]
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1 ≠ .start
    simp only [safeStep, if_neg hi]
    split <;> assumption
  halt_fixed := by
    intro a
    simp [transition, rawTransition, IntMul.TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1 = a 0
    rw [raw_input_readonly]
    exact IntMul.TapeAdder.safe_write_self _ _

def counterFrame (base : machine.Cfg) (q : State) (bits : List Bool) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then
    machine.tapeOf (Sym.sep :: (bits.reverse.map machine.bitSym ++ [Sym.sep])) else base.cells i
  head := fun i => if i = 2 then bits.length + 1 else base.head i

/-- Current decrement position: `bits` remain little-endian; the low-order
already-written suffix `done` is in tape order. -/
def carryFrame (base : machine.Cfg) (bits done : List Bool) : machine.Cfg where
  state := .carry
  cells := fun i => if i = 2 then
    machine.tapeOf (Sym.sep :: ((bits.reverse ++ done).map machine.bitSym ++ [Sym.sep])) else base.cells i
  head := fun i => if i = 2 then bits.length + 1 else base.head i

/-- Return right across the processed counter suffix. -/
def rewindFrame (base : machine.Cfg) (f : Bool) (pre right : List Bool) : machine.Cfg where
  state := .rewind f
  cells := fun i => if i = 2 then
    machine.tapeOf (Sym.sep :: ((pre ++ right).map machine.bitSym ++ [Sym.sep])) else base.cells i
  head := fun i => if i = 2 then pre.length + 2 else base.head i

/-- Saved-template reset frames. Counter and template words are in tape order. -/
def resetFrame (base : machine.Cfg) (q : State) (bits template : List Bool) (pos : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then
    machine.tapeOf (Sym.sep :: (bits.map machine.bitSym ++ [Sym.sep]))
    else if i = 3 then machine.tapeOf (Sym.sep :: (template.map machine.bitSym ++ [Sym.sep]))
    else base.cells i
  head := fun i => if i = 2 ∨ i = 3 then pos else base.head i


/-- Real output and prepared local countdown/template banks; input is arbitrary
and retained, including its head. No N-bit zero carry is supplied. -/
def initialFrame (base : machine.Cfg) (z : List Bool) : machine.Cfg where
  state := .start
  cells := fun i => if i=1 then machine.tapeOf []
    else if i=2 ∨ i=3 then machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep])) else base.cells i
  head := fun i => if i=1 then 0 else if i=2 ∨ i=3 then z.length+1 else base.head i

def frame (base : machine.Cfg) (z bits : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i=1 then machine.tapeOf ((List.replicate j false).map machine.bitSym)
    else if i=2 then machine.tapeOf (Sym.sep::(bits.reverse.map machine.bitSym++[Sym.sep]))
    else if i=3 then machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep])) else base.cells i
  head := fun i => if i=1 then j+1 else if i=2 ∨ i=3 then z.length+1 else base.head i

def finalFrame (base : machine.Cfg) (z : List Bool) : machine.Cfg :=
  frame base z z.reverse (val z+1) .halt
end IntMul.CountedZero


