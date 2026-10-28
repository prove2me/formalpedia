-- Prove2me | Definitions.Def_BitDFT_BufferShift
-- name    : BitDFT_BufferShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:01:08.886977+00:00
-- url     : https://prove2.me/theorems/3ebffab6-348a-41a2-8bb1-7f15a39eeb40
-- title:
--   In-place preparation of a child-machine input buffer
-- statement:
--   A fixed two-tape machine shifts a binary word on its mutable output tape one cell to the right, writes a trailing separator, and leaves a blank cell immediately after the permanent marker. Its native input tape and input head remain unchanged. The controller stores one bit while copying the word from right to left.
-- source:
--   Physical input-buffer preparation for the arbitrary Fourier-machine caller in the integer multiplication to finite-precision DFT transfer.

import Definitions.Def_BitDFT_HeaderReader
namespace BitDFT.BufferShift
open IntMul
abbrev Sym := TapeCopy.Sym
abbrev protect := HeaderReader.protect
inductive State
  | start | separator | left | read | write (b : Bool) | back | gap | halt
  deriving DecidableEq
instance : Fintype State where
  elems := {.start,.separator,.left,.read,.write false,.write true,.back,.gap,.halt}
  complete := by intro q; cases q <;> simp

def raw (q : State) (a : Fin 2 → Sym) : State × (Fin 2 → Sym × Move) :=
  match q with
  | .start => (.separator,fun i => (a i,if i = 1 then .right else .stay))
  | .separator => (.left,fun i => (if i = 1 then .sep else a i,if i = 1 then .left else .stay))
  | .left => (.read,fun i => (a i,if i = 1 then .left else .stay))
  | .read => if a 1 = .start then (.gap,fun i => (a i,if i = 1 then .right else .stay))
    else (.write (a 1 = .one),fun i => (a i,if i = 1 then .right else .stay))
  | .write b => (.back,fun i => (if i = 1 then (if b then .one else .zero) else a i,
      if i = 1 then .left else .stay))
  | .back => (.read,fun i => (a i,if i = 1 then .left else .stay))
  | .gap => (.halt,fun i => (if i = 1 then .blank else a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 2 → Sym) : State × (Fin 2 → Sym × Move) :=
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
  k := 2
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
    · exact protect_self _ _
    · split <;> exact protect_self _ _
    · exact protect_self _ _
    · exact protect_self _ _
    · exact protect_self _ _
    · exact protect_self _ _

def frame (base : machine.Cfg) (q : State) (out : List Sym) (hp : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 1 then machine.tapeOf out else base.cells i
  head := fun i => if i = 1 then hp else base.head i

def buffer (base : machine.Cfg) (q : State) (pre : List Bool) (gap : Sym) (post : List Bool) (hp : ℕ) : machine.Cfg :=
  frame base q (pre.map machine.bitSym ++ [gap] ++ post.map machine.bitSym ++ [TapeCopy.Sym.sep]) hp

end BitDFT.BufferShift


