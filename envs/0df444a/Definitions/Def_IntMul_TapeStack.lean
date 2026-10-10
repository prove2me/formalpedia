-- Prove2me | Definitions.Def_IntMul_TapeStack
-- name    : IntMul_TapeStack
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T21:42:39.160114+00:00
-- url     : https://prove2.me/theorems/6e009f92-5f50-4b93-94a1-cb0d1ec2e575
-- title:
--   Literal fixed four-tape stack push/pop with interior saved prefixes
-- statement:
--   Defines a literal one-way four-tape machine with five symbols and eight control states. Root input zero is frozen, mutable source/output is tape one, parking stack is tape two, and temporary storage is tape three. Push copies and erases the source word into the parked suffix, appends a separator and rewinds the source to its local separator. Pop erases the top delimiter, transfers and erases the parked word to temporary storage in reverse, reverses it physically back into output while erasing scratch, then rewinds output. Arbitrary saved prefixes and local offsets occur only in proof-side frames, absent from the finite table. The same table serves every stack depth; source/temporary/bank preparation and recursive scheduler composition remain separate obligations.
-- source:
--   Original actual one-way MultitapeTM formalization of the fixed-control stack push/pop strategy in CrocSwap/integer-mult-bounds research/machine-transfer-verification/transfer-proof/tapes/TapeStack*.lean, pinned at 3b6b66891c0ac888521cf591fe306c6286601d4f. Written by Codex.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.TapeStack

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep)

/-- One fixed finite control, shared by push and pop at every stack depth. -/
inductive State
  | pushCopy | pushRewind | popDelimiter | popPayload | popPark | popOutput | popRewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.pushCopy,.pushRewind,.popDelimiter,.popPayload,.popPark,.popOutput,.popRewind,.halt}
  complete := by intro q; cases q <;> simp

/-- Root input0 is frozen, source/output1, stack2, temporary3. No command
receives a tape position, ancestor length, word or recursion depth. -/
def rawTransition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt,fun i => (a i,.stay))
  | .pushCopy =>
      if a 1 = .zero ∨ a 1 = .one then
        (.pushCopy,fun i =>
          (if i = 1 then .blank else if i = 2 then a 1 else a i,
            if i = 1 ∨ i = 2 then .right else .stay))
      else (.pushRewind,fun i =>
        (if i = 2 then .sep else a i,
          if i = 1 then .left else if i = 2 then .right else .stay))
  | .pushRewind =>
      if a 1 = .sep then (.halt,fun i => (a i,if i = 1 then .right else .stay))
      else (.pushRewind,fun i => (a i,if i = 1 then .left else .stay))
  | .popDelimiter => (.popPayload,fun i => (a i,if i = 2 then .left else .stay))
  | .popPayload => (.popPark,fun i => (if i = 2 then .blank else a i,if i = 2 then .left else .stay))
  | .popPark =>
      if a 2 = .zero ∨ a 2 = .one then
        (.popPark,fun i =>
          (if i = 2 then .blank else if i = 3 then a 2 else a i,
            if i = 2 then .left else if i = 3 then .right else .stay))
      else if a 2 = .sep then
        (.popOutput,fun i => (a i,if i = 2 then .right else if i = 3 then .left else .stay))
      else (.halt,fun i => (a i,.stay))
  | .popOutput =>
      if a 3 = .zero ∨ a 3 = .one then
        (.popOutput,fun i =>
          (if i = 3 then .blank else if i = 1 then a 3 else a i,
            if i = 3 then .left else if i = 1 then .right else .stay))
      else if a 3 = .sep then
        (.popRewind,fun i => (a i,if i = 3 then .right else if i = 1 then .left else .stay))
      else (.halt,fun i => (a i,.stay))
  | .popRewind =>
      if a 1 = .sep then (.halt,fun i => (a i,if i = 1 then .right else .stay))
      else (.popRewind,fun i => (a i,if i = 1 then .left else .stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input_readonly (q : State) (a : Fin 4 → Sym) :
    ((rawTransition q a).2 0).1 = a 0 := by
  cases q <;> simp [rawTransition]
  all_goals repeat' first | rfl | split

/-- A literal one-way four-tape machine with five symbols and eight states.
The same table handles every number of older stack frames. -/
abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .pushCopy
  qHalt := .halt
  start_ne_halt := by decide
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1 = .start ∧ (safeStep (a i) _ _).2 ≠ .left
    rw [hi]
    simp only [safeStep,if_pos rfl]
    by_cases hd : ((rawTransition q a).2 i).2 = Move.left
    · simp [hd]
    · simp [hd]
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1 ≠ .start
    simp only [safeStep,if_neg hi]
    split <;> assumption
  halt_fixed := by intro a; simp [transition,rawTransition,IntMul.TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 _).1 = a 0
    rw [raw_input_readonly]
    exact IntMul.TapeAdder.safe_write_self _ _

/-- An interior word with a local separator boundary and arbitrary saved
prefix. Unlike the global start symbol, a separator is writable inside a tape. -/
def localTape (base : ℕ → Sym) (offset : ℕ) (w : List Sym) (p : ℕ) : Sym :=
  if p < offset then base p else if p = offset then .sep else w.getD (p - offset - 1) .blank

/-- Proof-side full frame. The three offsets and words never enter delta. -/
def frame (base : machine.Cfg) (q : State) (sigma rho tau : ℕ)
    (source stack temporary : List Sym) (a b c : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 1 then localTape (base.cells i) sigma source
    else if i = 2 then localTape (base.cells i) rho stack
    else if i = 3 then localTape (base.cells i) tau temporary else base.cells i
  head := fun i => if i = 1 then sigma + a else if i = 2 then rho + b
    else if i = 3 then tau + c else base.head i

/-- The prefix of copied payload cells is physically erased. -/
def erasedTape (base : ℕ → Sym) (offset : ℕ) (w : List Bool) (j p : ℕ) : Sym :=
  if p < offset then base p else if p = offset then .sep
    else if p < offset + j + 1 then .blank else (w.map machine.bitSym).getD (p - offset - 1) .blank

def pushFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (j : ℕ) : machine.Cfg where
  state := .pushCopy
  cells := fun i => if i = 1 then erasedTape (base.cells i) sigma w j
    else if i = 2 then localTape (base.cells i) rho ((w.take j).map machine.bitSym)
    else if i = 3 then localTape (base.cells i) tau [] else base.cells i
  head := fun i => if i = 1 then sigma + j + 1 else if i = 2 then rho + j + 1
    else if i = 3 then tau + 1 else base.head i

def pushRewindFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ) : machine.Cfg :=
  frame base .pushRewind sigma rho tau [] (w.map machine.bitSym ++ [.sep]) [] p (w.length + 2) 1

def pushDoneFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg :=
  frame base .halt sigma rho tau [] (w.map machine.bitSym ++ [.sep]) [] 1 (w.length + 2) 1

def popStartFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg :=
  frame base .popDelimiter sigma rho tau [] (w.map machine.bitSym ++ [.sep]) [] 1 (w.length + 2) 1

def popDelimiterFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg :=
  frame base .popPayload sigma rho tau [] (w.map machine.bitSym ++ [.sep]) [] 1 (w.length + 1) 1

def parkFrame (base : machine.Cfg) (sigma rho tau : ℕ) (left done : List Bool) : machine.Cfg :=
  frame base .popPark sigma rho tau [] (left.map machine.bitSym) (done.map machine.bitSym)
    1 left.length (done.length + 1)

def outputFrame (base : machine.Cfg) (sigma rho tau : ℕ) (left done : List Bool) : machine.Cfg :=
  frame base .popOutput sigma rho tau (done.map machine.bitSym) [] (left.map machine.bitSym)
    (done.length + 1) 1 left.length

def popRewindFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) (p : ℕ) : machine.Cfg :=
  frame base .popRewind sigma rho tau (w.map machine.bitSym) [] [] p 1 1

def popDoneFrame (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg :=
  frame base .halt sigma rho tau (w.map machine.bitSym) [] [] 1 1 1

end IntMul.TapeStack


