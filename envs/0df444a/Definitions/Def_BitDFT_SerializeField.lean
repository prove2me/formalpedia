-- Prove2me | Definitions.Def_BitDFT_SerializeField
-- name    : BitDFT_SerializeField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:20:01.481013+00:00
-- url     : https://prove2.me/theorems/1aca3938-1c7c-4e17-bdc7-8df261493ded
-- title:
--   Five-tape serializer for a retained binary field
-- statement:
--   A fixed five-tape machine appends the self-delimiting encoding of the word on tape 4 to the existing output on tape 1. It first moves backwards across the word while emitting its unary length, emits a zero delimiter, and then copies the word forwards. Native input and the other work tapes remain parked.
-- source:
--   Explicit serialization stage for the retained dimension and computed precision in the integer-multiplication-to-DFT request wrapper.

import Definitions.Def_BitDFT_HeaderReader
namespace BitDFT.SerializeField
open IntMul
abbrev Sym := TapeCopy.Sym
abbrev protect := HeaderReader.protect
inductive State
  | start | unary | copy | halt
  deriving DecidableEq
instance : Fintype State where
  elems := {.start,.unary,.copy,.halt}
  complete := by intro q; cases q <;> simp

/-- Emit a self-delimiting header from the word on tape 4, appending to output tape 1. -/
def raw (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  match q with
  | .start => (.unary,fun i => (a i,if i = 4 then .left else .stay))
  | .unary =>
    if a 4 = .start then (.copy,fun i => (if i = 1 then .zero else a i,
      if i = 1 ∨ i = 4 then .right else .stay))
    else (.unary,fun i => (if i = 1 then .one else a i,
      if i = 1 then .right else if i = 4 then .left else .stay))
  | .copy =>
    if a 4 = .zero ∨ a 4 = .one then (.copy,fun i => (if i = 1 then a 4 else a i,
      if i = 1 ∨ i = 4 then .right else .stay))
    else (.halt,fun i => (a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  ((raw q a).1,fun i => protect (a i) ((raw q a).2 i))

private theorem protect_self (a : Sym) (d : Move) : (protect a (a,d)).1 = a := by
  simp [protect,HeaderReader.protect]; split <;> simp_all

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
    simp only [transition, protect,HeaderReader.protect, hi, if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition, protect,HeaderReader.protect, hi, if_false]
    split <;> simp_all
  halt_fixed := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : a i = .start <;> simp [transition, raw, protect,HeaderReader.protect, h]
  input_readonly := by
    intro q a
    change (protect (a 0) ((raw q a).2 0)).1 = a 0
    cases q <;> simp only [raw]
    · exact protect_self _ _
    · split <;> exact protect_self _ _
    · split <;> exact protect_self _ _
    · exact protect_self _ _

def frame (base : machine.Cfg) (q : State) (v out : List Bool) (h4 : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 1 then machine.tapeOf (out.map machine.bitSym)
    else if i = 4 then machine.tapeOf (v.map machine.bitSym) else base.cells i
  head := fun i => if i = 1 then out.length+1 else if i = 4 then h4 else base.head i
end BitDFT.SerializeField


