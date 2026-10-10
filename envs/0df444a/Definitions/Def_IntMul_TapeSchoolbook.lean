-- Prove2me | Definitions.Def_IntMul_TapeSchoolbook
-- name    : IntMul_TapeSchoolbook
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T20:33:37.082729+00:00
-- url     : https://prove2.me/theorems/cce0a581-1a2e-4898-ba0b-ae5d405e1113
-- title:
--   Literal four-tape fixed-width shift-and-add integer multiplier
-- statement:
--   A single deterministic four-tape, five-symbol, nineteen-state machine in the campaign's one-sided MultitapeTM model. Its literal transition table pads and copies the operands, scans the multiplier from most significant to least significant, shifts the accumulator, conditionally ripple-adds the padded first operand, returns each arithmetic head, and physically erases the output delimiter before halting. It reads only finite state and currently scanned symbols. Configuration frames and exact proof-side clocks describe its traces; no width, head-position, numeric, or multiplication oracle occurs in its transition table.
-- source:
--   Classical schoolbook shift-and-add multiplication, implementing existing IntMul.TM.schoolbook milestone 86109c88-e1e4-410a-a312-0a5f005a04cf. Written by Codex.

import Definitions.Def_IntMul_TapeAdder
import Definitions.Def_IntMul_BinarySchoolbook

namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep encode decode)

inductive State
  | start | padX | rewindInput | copyX | copyY | rewindY | next
  | shift (add previous : Bool) | rewindShift (add : Bool)
  | add (carry : Bool) | rewindAdd | advance | erase | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start,.padX,.rewindInput,.copyX,.copyY,.rewindY,.next,
    .shift false false,.shift false true,.shift true false,.shift true true,
    .rewindShift false,.rewindShift true,.add false,.add true,
    .rewindAdd,.advance,.erase,.halt}
  complete := by
    intro q
    cases q <;> simp
    all_goals repeat' first | rename_i b; cases b <;> simp

/-- Tapes are input (0), product/output (1), padded first operand (2), and
multiplier (3). All arithmetic scans use only the currently scanned symbols. -/
def rawTransition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt,fun i => (a i,.stay))
  | .start => (.padX,fun i => (a i,.right))
  | .padX =>
      if a 0 = .zero ∨ a 0 = .one then
        (.padX,fun i => (if i = 1 ∨ i = 2 then .zero else a i,
          if i = 0 ∨ i = 1 ∨ i = 2 then .right else .stay))
      else (.rewindInput,fun i => (a i,if i = 0 then .left else .stay))
  | .rewindInput =>
      if a 0 = .start then (.copyX,fun i => (a i,if i = 0 then .right else .stay))
      else (.rewindInput,fun i => (a i,if i = 0 then .left else .stay))
  | .copyX =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copyX,fun i => (if i = 1 then .zero else if i = 2 then a 0 else a i,
          if i = 0 ∨ i = 1 ∨ i = 2 then .right else .stay))
      else (.copyY,fun i => (if i = 1 ∨ i = 2 then .sep else a i,
        if i = 0 then .right else if i = 1 ∨ i = 2 then .left else .stay))
  | .copyY =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copyY,fun i => (if i = 3 then a 0 else a i,if i = 0 ∨ i = 3 then .right else .stay))
      else (.rewindY,fun i => (if i = 3 then .sep else a i,if i = 3 then .left else .stay))
  | .rewindY =>
      if a 3 = .start then (.next,fun i => (a i,if i = 3 then .right else .stay))
      else (.rewindY,fun i => (a i,if i = 3 then .left else .stay))
  | .next =>
      if a 3 = .zero ∨ a 3 = .one then (.shift (decode (a 3)) false,fun i => (a i,.stay))
      else (.erase,fun i => (a i,if i = 1 then .right else .stay))
  | .shift add previous =>
      if a 1 = .start then (.rewindShift add,fun i => (a i,if i = 1 then .right else .stay))
      else (.shift add (decode (a 1)),fun i => (if i = 1 then encode previous else a i,
        if i = 1 then .left else .stay))
  | .rewindShift add =>
      if a 1 = .zero ∨ a 1 = .one then (.rewindShift add,fun i => (a i,if i = 1 then .right else .stay))
      else (if add then .add false else .advance,fun i => (a i,if i = 1 then .left else .stay))
  | .add carry =>
      if a 1 = .start then (.rewindAdd,fun i => (a i,if i = 1 ∨ i = 2 then .right else .stay))
      else (.add (BinaryAdder.carryBit (decode (a 1)) (decode (a 2)) carry),fun i =>
        (if i = 1 then encode (BinaryAdder.sumBit (decode (a 1)) (decode (a 2)) carry) else a i,
          if i = 1 ∨ i = 2 then .left else .stay))
  | .rewindAdd =>
      if a 1 = .zero ∨ a 1 = .one then (.rewindAdd,fun i => (a i,if i = 1 ∨ i = 2 then .right else .stay))
      else (.advance,fun i => (a i,if i = 1 ∨ i = 2 then .left else .stay))
  | .advance => (.next,fun i => (a i,if i = 3 then .right else .stay))
  | .erase => (.halt,fun i => (if i = 1 then .blank else a i,.stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

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
    simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1 = a 0
    rw [raw_input_readonly]
    exact TapeAdder.safe_write_self _ _

/-- A multiplication-loop boundary. Product and padded first operand are
right-delimited; the multiplier head is on its next most significant bit. -/
def readyFrame (x y p : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf (p.map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf ((List.replicate x.length false ++ x).map machine.bitSym ++ [Sym.sep])
    else machine.tapeOf (y.map machine.bitSym ++ [Sym.sep])
  head := fun i =>
    if i = 0 then x.length + y.length + 2
    else if i = 1 then p.length
    else if i = 2 then 2 * x.length
    else j + 1

/-- A product-tape phase with arbitrary saved contents/heads on other tapes. -/
def productFrame (base : machine.Cfg) (q : State) (p : List Bool) (pos : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 1 then machine.tapeOf (p.map machine.bitSym ++ [Sym.sep]) else base.cells i
  head := fun i => if i = 1 then pos else base.head i

/-- Both arithmetic heads at the same supplied position, with the exact
product and unmodified padded first operand recorded in tape order. -/
def arithmeticFrame (base : machine.Cfg) (q : State) (p x : List Bool) (pos : ℕ) : machine.Cfg where
  state := q
  cells := fun i =>
    if i = 1 then machine.tapeOf (p.map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf (x.map machine.bitSym ++ [Sym.sep])
    else base.cells i
  head := fun i => if i = 1 ∨ i = 2 then pos else base.head i

/-- A least-significant-first shift, recording the already written suffix in
tape order. The other tapes and heads retain the arbitrary base configuration. -/
def shiftFrame (base : machine.Cfg) (add previous : Bool) (bits done : List Bool) : machine.Cfg where
  state := .shift add previous
  cells := fun i => if i = 1 then
    machine.tapeOf ((bits.reverse ++ done).map machine.bitSym ++ [Sym.sep]) else base.cells i
  head := fun i => if i = 1 then bits.length else base.head i

/-- Return the product head across an unchanged shifted word. -/
def returnShiftFrame (base : machine.Cfg) (add : Bool) (pre right : List Bool) : machine.Cfg where
  state := .rewindShift add
  cells := fun i => if i = 1 then
    machine.tapeOf ((pre ++ right).map machine.bitSym ++ [Sym.sep]) else base.cells i
  head := fun i => if i = 1 then pre.length + 1 else base.head i

/-- A physical fixed-width ripple addition; the first-operand tape is read
unchanged while its head moves with the product head. -/
def addFrame (base : machine.Cfg) (carry : Bool) (p x doneP doneX : List Bool) : machine.Cfg where
  state := .add carry
  cells := fun i =>
    if i = 1 then machine.tapeOf ((p.reverse ++ doneP).map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf ((x.reverse ++ doneX).map machine.bitSym ++ [Sym.sep])
    else base.cells i
  head := fun i => if i = 1 then p.length else if i = 2 then x.length else base.head i

/-- Return both arithmetic heads to the least significant positions. -/
def returnAddFrame (base : machine.Cfg) (pre right x : List Bool) : machine.Cfg where
  state := .rewindAdd
  cells := fun i =>
    if i = 1 then machine.tapeOf ((pre ++ right).map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf (x.map machine.bitSym ++ [Sym.sep])
    else base.cells i
  head := fun i => if i = 1 ∨ i = 2 then pre.length + 1 else base.head i

/-- The final output separator has been physically erased. -/
def finalFrame (x y p : List Bool) : machine.Cfg where
  state := .halt
  cells := fun i => if i = 1 then machine.tapeOf (p.map machine.bitSym)
    else (readyFrame x y p y.length .halt).cells i
  head := fun i => if i = 1 then p.length + 1
    else (readyFrame x y p y.length .halt).head i

/-- Proof-side exact clocks; the transition table does not read these values. -/
def iterationSteps (width : ℕ) (b : Bool) : ℕ := if b then 4 * width + 6 else 2 * width + 4

def loopSteps (width : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs => iterationSteps width b + loopSteps width bs

end IntMul.TapeSchoolbook


