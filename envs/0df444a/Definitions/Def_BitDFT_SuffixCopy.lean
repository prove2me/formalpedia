-- Prove2me | Definitions.Def_BitDFT_SuffixCopy
-- name    : BitDFT_SuffixCopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:36:21.032325+00:00
-- url     : https://prove2.me/theorems/a6e5ccab-1d56-408d-af71-d0f0f8c199b7
-- title:
--   Five-tape native-input suffix copying machine
-- statement:
--   A fixed machine appends native input bits to native output until the input separator, preserving all work tapes and their heads. The frame specifies the full native input, the existing output prefix, and the input head position.
-- source:
--   Final vector-copying stage of the precision-header rewriting preprocessor.

import Definitions.Def_BitDFT_HeaderReader
namespace BitDFT.SuffixCopy
open IntMul
abbrev Sym := TapeCopy.Sym
abbrev protect := HeaderReader.protect
inductive State | copy | halt deriving DecidableEq
instance : Fintype State where
  elems := {.copy,.halt}
  complete := by intro q; cases q <;> simp

def raw (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  match q with
  | .copy => if a 0 = .zero ∨ a 0 = .one then
      (.copy,fun i => (if i = 1 then a 0 else a i,if i = 0 ∨ i = 1 then .right else .stay))
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
  qStart := .copy
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
    · split <;> exact protect_self _ _
    · exact protect_self _ _

def frame (base : machine.Cfg) (q : State) (input out : List Bool) (ip : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then machine.tapeOf (input.map machine.bitSym ++ [TapeCopy.Sym.sep])
    else if i = 1 then machine.tapeOf (out.map machine.bitSym) else base.cells i
  head := fun i => if i = 0 then ip else if i = 1 then out.length+1 else base.head i

end BitDFT.SuffixCopy


