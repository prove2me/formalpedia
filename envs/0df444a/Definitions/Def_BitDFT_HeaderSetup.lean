-- Prove2me | Definitions.Def_BitDFT_HeaderSetup
-- name    : BitDFT_HeaderSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:00:49.019984+00:00
-- url     : https://prove2.me/theorems/d8f1741e-9a84-44c9-8165-3ea18233acba
-- title:
--   Five-tape machine for installing parsed precision bits
-- statement:
--   A fixed five-tape machine reverses a binary field from tape 3 into tape 2, clearing tape 3 as it copies, and rewinds the retained dimension on tape 4. It preserves native input/output tapes and their heads. Its frame definition specifies every tape cell and head position.
-- source:
--   Preparation stage connecting parsed request headers to the existing guard-precision computation program.

import Definitions.Def_BitDFT_HeaderReader

namespace BitDFT.HeaderSetup
open IntMul
abbrev Sym := IntMul.TapeCopy.Sym
abbrev protect := HeaderReader.protect

inductive State
  | start | copy | rewind2 | rewind4 | halt
  deriving DecidableEq
instance : Fintype State where
  elems := {.start, .copy, .rewind2, .rewind4, .halt}
  complete := by intro q; cases q <;> simp

/-- Reverse the retained precision field into tape 2, clear tape 3, and rewind the dimension. -/
def raw (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  match q with
  | .start => (.copy, fun i => (a i, if i = 2 then .right else if i = 3 then .left else .stay))
  | .copy =>
    if a 3 = .zero ∨ a 3 = .one then
      (.copy, fun i => (if i = 2 then a 3 else if i = 3 then .blank else a i,
        if i = 2 then .right else if i = 3 then .left else .stay))
    else (.rewind2, fun i => (a i, if i = 2 then .left else .stay))
  | .rewind2 =>
    if a 2 = .start then (.rewind4, fun i => (a i, if i = 4 then .left else .stay))
    else (.rewind2, fun i => (a i, if i = 2 then .left else .stay))
  | .rewind4 =>
    if a 4 = .start then (.halt, fun i => (a i, if i = 2 ∨ i = 3 ∨ i = 4 then .right else .stay))
    else (.rewind4, fun i => (a i, if i = 4 then .left else .stay))
  | .halt => (.halt, fun i => (a i, .stay))

def transition (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  ((raw q a).1, fun i => protect (a i) ((raw q a).2 i))

private theorem protect_self (a : Sym) (d : Move) : (protect a (a,d)).1 = a := by
  simp [protect, HeaderReader.protect]; split <;> simp_all

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
  k := 5
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    simp only [transition, protect, HeaderReader.protect, hi, if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition, protect, HeaderReader.protect, hi, if_false]
    split <;> simp_all
  halt_fixed := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : a i = .start <;> simp [transition, raw, protect, HeaderReader.protect, h]
  input_readonly := by
    intro q a
    change (protect (a 0) ((raw q a).2 0)).1 = a 0
    cases q <;> simp only [raw]
    · exact protect_self _ _
    · split <;> exact protect_self _ _
    · split <;> exact protect_self _ _
    · split <;> exact protect_self _ _
    · exact protect_self _ _

/-- Work-tape layout while preparing the precision program; native tapes are preserved. -/
def frame (base : machine.Cfg) (q : State) (src dst dim : List Bool) (h2 h3 h4 : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then machine.tapeOf (dst.map machine.bitSym)
    else if i = 3 then machine.tapeOf (src.map machine.bitSym)
    else if i = 4 then machine.tapeOf (dim.map machine.bitSym) else base.cells i
  head := fun i => if i = 2 then h2 else if i = 3 then h3 else if i = 4 then h4 else base.head i

end BitDFT.HeaderSetup


