-- Prove2me | Definitions.Def_BitDFT_LogScanner
-- name    : BitDFT_LogScanner
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T15:07:45.070762+00:00
-- url     : https://prove2.me/theorems/8138874a-e911-452a-bc63-440f67cda233
-- title:
--   A finite scanner preparing the unary logarithmic precision increment
-- statement:
--   A fixed four-tape machine scans a canonical binary dimension word on work tape 2 and writes a unary increment on work tape 3. It skips the leading one, writes three marks for each remaining bit, and tracks whether any remaining bit is one. It then appends five marks when the tail is nonempty and all zero, and eight marks otherwise. It preserves the dimension word and arbitrary native input/output data. The final unary head rests on the last mark, matching the binary-counter calling convention. All padding counts are bounded by eight in the finite control.
-- source:
--   Original finite scan for the guard-precision wrapper. It reuses the existing alphabet and marker-protection function and provides an explicit preparation stage for the proved binary counter.

import Definitions.Def_BitDFT_HeaderReader
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

namespace BitDFT.LogScanner
open IntMul
abbrev Sym := TapeCopy.Sym
inductive State
  | start | scan (seen one : Bool) | write2 (one : Bool) | write1 (one : Bool)
  | pad (left : Fin 9) | halt
  deriving DecidableEq, Fintype

def emit (q : State) (a : Fin 4 → Sym) (advance : Bool) : State × (Fin 4 → Sym × Move) :=
  (q, fun i => if i = 3 then (.one,.right)
    else (a i,if i = 2 ∧ advance then .right else .stay))

def extra (seen one : Bool) : Fin 9 := if seen && !one then ⟨5,by decide⟩ else ⟨8,by decide⟩

def raw (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .start => (.scan false false,fun i => (a i,if i = 2 then .right else .stay))
  | .scan seen one => if a 2 = .zero ∨ a 2 = .one then
      emit (.write2 (one || decide (a 2 = .one))) a true
    else (.pad (extra seen one),fun i => (a i,.stay))
  | .write2 one => emit (.write1 one) a false
  | .write1 one => emit (.scan true one) a false
  | .pad j => if h : j.val = 0 then (.halt,fun i => (a i,if i = 3 then .left else .stay))
    else emit (.pad ⟨j.val-1,by omega⟩) a false
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  ((raw q a).1,fun i => HeaderReader.protect (a i) ((raw q a).2 i))

private theorem protect_stay (a : Sym) : HeaderReader.protect a (a,.stay) = (a,.stay) := by
  cases a <;> rfl

private theorem raw_input (q : State) (a : Fin 4 → Sym) : (raw q a).2 0 = (a 0,.stay) := by
  cases q with
  | start => rfl
  | scan seen one => simp only [raw]; split <;> simp [emit]
  | write2 one => simp [raw,emit]
  | write1 one => simp [raw,emit]
  | pad j => simp only [raw]; split <;> simp [emit]
  | halt => rfl

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
    simp only [transition,HeaderReader.protect,hi,if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition,HeaderReader.protect,hi,if_false]
    split <;> simp_all
  halt_fixed := by
    intro a
    apply Prod.ext
    · rfl
    · funext i; exact protect_stay _
  input_readonly := by
    intro q a
    change (HeaderReader.protect (a 0) ((raw q a).2 0)).1 = a 0
    rw [raw_input,protect_stay]

/-- Work tape 2 is scanned without changes; work tape 3 receives the unary increment. -/
def frame (base : machine.Cfg) (q : State) (w : List Bool) (ip count hp : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then machine.tapeOf (w.map machine.bitSym)
    else if i = 3 then machine.tapeOf (List.replicate count TapeCopy.Sym.one)
    else base.cells i
  head := fun i => if i = 2 then ip else if i = 3 then hp else base.head i

end BitDFT.LogScanner


