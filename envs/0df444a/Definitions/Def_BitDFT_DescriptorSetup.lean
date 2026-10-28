-- Prove2me | Definitions.Def_BitDFT_DescriptorSetup
-- name    : BitDFT_DescriptorSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:03:09.200492+00:00
-- url     : https://prove2.me/theorems/ab40d531-241f-4a16-a554-9774bf6d47cb
-- title:
--   A machine preparing countdown and template tapes from a binary precision word
-- statement:
--   A four-tape machine parks native tape zero, reads a binary word from tape one, and copies it to tapes two and three between separator symbols. Its initial configuration has both target tapes blank with heads at their markers and the source head on its first bit. The final configuration preserves the source and native tape, with both target heads at the low-order end of the copied words.
-- source:
--   Charged descriptor preparation for the exact Fourier output scaler.

import Definitions.Def_BitDFT_HeaderReader
namespace BitDFT.DescriptorSetup
open IntMul
abbrev Sym := TapeCopy.Sym
abbrev protect := HeaderReader.protect
inductive State | start | mark | copy | halt deriving DecidableEq
instance : Fintype State where
  elems := {.start,.mark,.copy,.halt}
  complete := by intro q; cases q <;> simp

def raw (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .start => (.mark,fun i => (a i,if i = 2 ∨ i = 3 then .right else .stay))
  | .mark => (.copy,fun i => (if i = 2 ∨ i = 3 then .sep else a i,
      if i = 2 ∨ i = 3 then .right else .stay))
  | .copy => if a 1 = .zero ∨ a 1 = .one then
      (.copy,fun i => (if i = 2 ∨ i = 3 then a 1 else a i,
        if i = 0 then .stay else .right))
    else (.halt,fun i => (if i = 2 ∨ i = 3 then .sep else a i,
      if i = 2 ∨ i = 3 then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
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
  k := 4
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
    · exact protect_self _ _
    · split <;> exact protect_self _ _
    · exact protect_self _ _


def initial (base : machine.Cfg) (y : List Bool) : machine.Cfg where
  state := .start
  cells := fun i => if i = 1 then machine.tapeOf (y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf [] else base.cells i
  head := fun i => if i = 1 then 1 else if i = 2 ∨ i = 3 then 0 else base.head i

def frame (base : machine.Cfg) (y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copy
  cells := fun i => if i = 1 then machine.tapeOf (y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (.sep :: (y.take j).map machine.bitSym)
    else base.cells i
  head := fun i => if i = 1 then j+1 else if i = 2 ∨ i = 3 then j+2 else base.head i

def final (base : machine.Cfg) (y : List Bool) : machine.Cfg where
  state := .halt
  cells := fun i => if i = 1 then machine.tapeOf (y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (.sep :: (y.map machine.bitSym ++ [.sep]))
    else base.cells i
  head := fun i => if i = 0 then base.head i else y.length+1

end BitDFT.DescriptorSetup


