-- Prove2me | Definitions.Def_BitDFT_TrimReverse
-- name    : BitDFT_TrimReverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:26:47.323643+00:00
-- url     : https://prove2.me/theorems/06ed0b9f-e2e3-4e2f-9eaf-a11a0e7c19bb
-- title:
--   Five-tape normalization of a padded little-endian binary word
-- statement:
--   A fixed machine scans the little-endian word on tape 2, erases high zero padding, and copies the remaining bits backwards onto tape 3 while clearing tape 2. It preserves native input/output and tape 4. Its initial layout places the source head at its first cell and the empty destination head on its marker.
-- source:
--   Canonicalization stage for the computed precision before self-delimiting header serialization.

import Definitions.Def_BitDFT_HeaderReader
namespace BitDFT.TrimReverse
open IntMul
abbrev Sym := TapeCopy.Sym
abbrev protect := HeaderReader.protect
inductive State
  | start | scan | trim | copy | halt
  deriving DecidableEq
instance : Fintype State where
  elems := {.start,.scan,.trim,.copy,.halt}
  complete := by intro q; cases q <;> simp

def raw (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  match q with
  | .start => (.scan,fun i => (a i,if i = 3 then .right else .stay))
  | .scan => if a 2 = .zero ∨ a 2 = .one then
      (.scan,fun i => (a i,if i = 2 then .right else .stay))
    else (.trim,fun i => (a i,if i = 2 then .left else .stay))
  | .trim => if a 2 = .zero then
      (.trim,fun i => (if i = 2 then .blank else a i,if i = 2 then .left else .stay))
    else (.copy,fun i => (a i,.stay))
  | .copy => if a 2 = .start then (.halt,fun i => (a i,.stay))
    else (.copy,fun i => (if i = 2 then .blank else if i = 3 then a 2 else a i,
      if i = 2 then .left else if i = 3 then .right else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 5 → Sym) : State × (Fin 5 → Sym × Move) :=
  ((raw q a).1,fun i => protect (a i) ((raw q a).2 i))

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

def frame (base : machine.Cfg) (q : State) (src dst : List Bool) (hp : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then machine.tapeOf (src.map machine.bitSym)
    else if i = 3 then machine.tapeOf (dst.map machine.bitSym) else base.cells i
  head := fun i => if i = 2 then hp else if i = 3 then dst.length+1 else base.head i

def initial (base : machine.Cfg) (w : List Bool) : machine.Cfg where
  state := .start
  cells := (frame base .start w [] 1).cells
  head := fun i => if i = 2 then 1 else if i = 3 then 0 else base.head i

end BitDFT.TrimReverse


