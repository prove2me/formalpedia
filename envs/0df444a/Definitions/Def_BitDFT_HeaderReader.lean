-- Prove2me | Definitions.Def_BitDFT_HeaderReader
-- name    : BitDFT_HeaderReader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T13:52:52.632502+00:00
-- url     : https://prove2.me/theorems/131aa81f-d164-45d6-8ada-9418abc9d99c
-- title:
--   A fixed four-tape reader for length-prefixed binary fields
-- statement:
--   A deterministic four-tape Turing machine reads a field encoded as a unary length prefix, a zero delimiter, and that many binary payload bits. It retains the field on a separate work tape, erases the unary counter, and copies the remaining input to the native output. The finite transition table handles all field lengths with the same five control states. This is an input-parsing component for the finite-precision Fourier wrapper; the complete wrapper is a separate construction.
-- source:
--   Original finite-tape header reader for the BitDFT encoding. Uses the alphabet of IntMul_TapeCopy (definition 90b8eb1e-ba7f-4c64-832b-51fc4af20cbf) and the exact IntMul.MultitapeTM transition semantics. The proof adapts finite-tape write invariants from https://prove2.me/submissions/69d83c43-de72-4472-86ad-45f6ea010014.

import Definitions.Def_IntMul_TapeCopy

namespace BitDFT.HeaderReader
open IntMul
abbrev Sym := IntMul.TapeCopy.Sym

inductive State
  | start | prefix | value | copy | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .prefix, .value, .copy, .halt}
  complete := by intro q; cases q <;> simp

def protect (a : Sym) (w : Sym × Move) : Sym × Move :=
  if a = .start then (.start, if w.2 = .left then .stay else w.2)
  else (if w.1 = .start then a else w.1, w.2)

/-- Four fixed tapes: native input/output, a unary length counter, and the decoded field. -/
def raw (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .start => (.prefix, fun i => (a i, .right))
  | .prefix =>
    if a 0 = .one then
      (.prefix, fun i => (if i = 2 then .one else a i,
        if i = 0 ∨ i = 2 then .right else .stay))
    else (.value, fun i => (a i, if i = 0 then .right else if i = 2 then .left else .stay))
  | .value =>
    if a 2 = .start then (.copy, fun i => (a i, .stay))
    else (.value, fun i => (if i = 2 then .blank else if i = 3 then a 0 else a i,
      if i = 0 ∨ i = 3 then .right else if i = 2 then .left else .stay))
  | .copy =>
    if a 0 = .zero ∨ a 0 = .one then
      (.copy, fun i => (if i = 1 then a 0 else a i,
        if i = 0 ∨ i = 1 then .right else .stay))
    else (.halt, fun i => (a i, .stay))
  | .halt => (.halt, fun i => (a i, .stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  ((raw q a).1, fun i => protect (a i) ((raw q a).2 i))

private theorem protect_self (a : Sym) (d : Move) : (protect a (a,d)).1 = a := by
  simp [protect]; split <;> simp_all

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
    simp only [transition, protect, hi, if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition, protect, hi, if_false]
    split <;> simp_all
  halt_fixed := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : a i = .start <;> simp [transition, raw, protect, h]
  input_readonly := by
    intro q a
    change (protect (a 0) ((raw q a).2 0)).1 = a 0
    cases q <;> simp only [raw]
    · exact protect_self _ _
    · split <;> exact protect_self _ _
    · split <;> exact protect_self _ _
    · split <;> exact protect_self _ _
    · exact protect_self _ _

end BitDFT.HeaderReader


