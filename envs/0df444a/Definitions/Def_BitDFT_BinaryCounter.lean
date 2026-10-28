-- Prove2me | Definitions.Def_BitDFT_BinaryCounter
-- name    : BitDFT_BinaryCounter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:47:40.915534+00:00
-- url     : https://prove2.me/theorems/8b9569df-f149-439d-8c00-25d163921d9b
-- title:
--   A finite binary counter controlled by a unary work-tape count
-- statement:
--   A fixed four-tape machine adds a unary count to a little-endian binary word. Work tape 2 holds the binary word with its head on the least significant bit; work tape 3 holds a unary count with its head on the last mark. Each cycle erases one mark, propagates a carry, and returns the binary head to its first bit. It halts when the unary count is exhausted. The native input and output tapes are preserved. The same finite transition table handles all word lengths and count values.
-- source:
--   Original finite binary-counter routine for computing the BitDFT working precision. Uses the existing multitape model and marker-protection function. The pure little-endian value, increment, and potential definitions state its numerical and runtime invariants.

import Definitions.Def_BitDFT_HeaderReader
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace BitDFT.BinaryCounter
open IntMul
abbrev Sym := TapeCopy.Sym
inductive State | tick | carry | rewind | halt deriving DecidableEq
instance : Fintype State where
  elems := {.tick,.carry,.rewind,.halt}
  complete := by intro s; cases s <;> simp

def raw (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i,.stay))
  | .tick => if a 3 = .start then (.halt, fun i => (a i,.stay))
      else (.carry, fun i => if i = 3 then (.blank,.left) else (a i,.stay))
  | .carry => if a 2 = .one then
      (.carry, fun i => if i = 2 then (.zero,.right) else (a i,.stay))
      else (.rewind, fun i => if i = 2 then (.one,.left) else (a i,.stay))
  | .rewind => if a 2 = .start then
      (.tick, fun i => (a i, if i = 2 then .right else .stay))
      else (.rewind, fun i => (a i, if i = 2 then .left else .stay))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  ((raw q a).1, fun i => HeaderReader.protect (a i) ((raw q a).2 i))

private theorem protect_self (a : Sym) : HeaderReader.protect a (a,.stay) = (a,.stay) := by
  cases a <;> rfl

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .tick
  qHalt := .halt
  start_ne_halt := by decide
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    simp only [transition, HeaderReader.protect, hi, if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition, HeaderReader.protect, hi, if_false]
    split <;> simp_all
  halt_fixed := by
    intro a
    apply Prod.ext
    · rfl
    · funext i; exact protect_self _
  input_readonly := by
    intro q a
    cases q <;> simp only [transition, raw]
    · split <;> exact congrArg Prod.fst (protect_self _)
    · split <;> exact congrArg Prod.fst (protect_self _)
    · split <;> exact congrArg Prod.fst (protect_self _)
    · exact congrArg Prod.fst (protect_self _)

/-- Little-endian increment, retaining any high zero padding. -/
def increment : List Bool → List Bool
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: increment w

def lowOnes : List Bool → ℕ
  | true :: w => lowOnes w + 1
  | _ => 0

def ones : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + ones w

def value : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2*value w

/-- Only work tapes 2 and 3 change; root input and output are arbitrary parked caller data. -/
def frame (base : machine.Cfg) (q : State) (w : List Bool) (k hp : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 2 then machine.tapeOf (w.map machine.bitSym)
    else if i = 3 then machine.tapeOf (List.replicate k TapeCopy.Sym.one)
    else base.cells i
  head := fun i => if i = 2 then hp else if i = 3 then k else base.head i

end BitDFT.BinaryCounter


