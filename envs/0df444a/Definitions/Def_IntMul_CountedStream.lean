-- Prove2me | Definitions.Def_IntMul_CountedStream
-- name    : IntMul_CountedStream
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T19:10:37.240193+00:00
-- url     : https://prove2.me/theorems/723d7ca2-45b0-4591-a33b-a9e61e93fa47
-- title:
--   A literal counted-stream controller with saved-template reset
-- statement:
--   Defines one fixed thirteen-state, four-tape controller in the campaign’s actual multitape model: input, output, countdown, and saved-template tapes. Its finite table initializes a delimited countdown from the second operand, emits payload bits, physically decrements the counter, dispatches according to underflow, and restores the counter from the saved template before halting. It also defines tape configurations for the decrement and reset phases and their elementary finite-word accounting. These configurations specify tape contents and positions; the transition table itself sees only state and scanned symbols. All start-marker, input read-only, and frozen-halt conditions are checked. Correctness and costs of the actual decrement, template reset, and full controller are separate proof obligations.
-- source:
--   Counter arithmetic and amortized decrement analysis adapted from CrocSwap/integer-mult-bounds at 3b6b66891c0ac888521cf591fe306c6286601d4f, research/machine-transfer-verification/stream-transfer/counters/CounterArithmetic.lean and RippleCounter.lean (Apache-2.0). https://github.com/CrocSwap/integer-mult-bounds/tree/3b6b66891c0ac888521cf591fe306c6286601d4f/research/machine-transfer-verification/stream-transfer/counters . Their README explicitly leaves payload/reset/dispatcher composition outside its cost theorem. This finite table implements those phases in the campaign’s one-sided MultitapeTM model, reversing the counter orientation to fit the big-endian input descriptor. No claim is made of a new counter algorithm.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep encode decode)

/-- Literal stream controller, counter, and saved-template reset states. -/
inductive State
  | start | scanX | copyY | rewindInput | emit | carry
  | rewind (underflow : Bool) | done (underflow : Bool)
  | resetLeft | resetRight | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .scanX, .copyY, .rewindInput, .emit, .carry,
    .rewind false, .rewind true, .done false, .done true, .resetLeft, .resetRight, .halt}
  complete := by
    intro q
    cases q <;> simp

/-- Each command uses only finite state and currently scanned symbols.
Tape 0 is input, 1 is output, 2 is countdown, 3 is the local saved template. -/
def rawTransition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i, .stay))
  | .start => (.scanX, fun i => (a i, .right))
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
  | .emit =>
      if a 0 = .zero ∨ a 0 = .one then
        (.carry, fun i => (if i = 1 then a 0 else a i,
          if i = 0 ∨ i = 1 then .right else .stay))
      else (.halt, fun i => (a i, .stay))
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

/-- Number of low-order zeros through which a decrement propagates. -/
def carryLength : List Bool → ℕ
  | [] => 0
  | b :: bs => if b = false then carryLength bs + 1 else 0

def stopTail : List Bool → List Bool
  | [] => []
  | b :: bs => if b = false then stopTail bs else (!b) :: bs

def underflow : List Bool → Bool
  | [] => true
  | b :: bs => if b = false then underflow bs else false

/-- Little-endian fixed-width decrement output. -/
def updated (bits : List Bool) : List Bool :=
  List.replicate (carryLength bits) true ++ stopTail bits

def counterSteps (bits : List Bool) : ℕ := 2 * carryLength bits + 2

def iterateCounter : ℕ → List Bool → List Bool
  | 0, bits => bits
  | n + 1, bits => iterateCounter n (updated bits)

def totalCounterSteps : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, bits => counterSteps bits + totalCounterSteps n (updated bits)


abbrev value : List Bool → ℕ := IntMul.BinaryAdder.littleVal

/-- Credit for a decrement is the number of zero bits. -/
def potential : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b = false then 1 else 0) + potential bs


/-- Counter words are delimited on the working tape. Other tapes and heads
come from the arbitrary saved configuration `base`. -/
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

end IntMul.CountedStream


