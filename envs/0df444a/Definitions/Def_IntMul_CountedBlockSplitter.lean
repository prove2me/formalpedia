-- Prove2me | Definitions.Def_IntMul_CountedBlockSplitter
-- name    : IntMul_CountedBlockSplitter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T08:31:44.27837+00:00
-- url     : https://prove2.me/theorems/37826494-5446-40f8-9977-1b2da2853785
-- title:
--   Fixed-tape descriptor-sized digit block splitter
-- statement:
--   A single fixed four-tape, five-symbol, 29-state multitape Turing machine splits an arbitrary binary input payload into consecutive B-bit blocks, where B=val(y)+1 is encoded by the descriptor y. It borrows the counted stream service and adds one actual separator-writing state, with a finite caller bit for final template cleanup. The transition table uses only finite states and scanned symbols; it never reads payload length, descriptor value, or head coordinates. Defines the exact separated raw-symbol output prefix, with no trailing separator, and the full restored descriptor boundary frame. Correctness and global execution time are separate theorem obligations.
-- source:
--   Original block-separator service and finite caller composition using the accepted counted stream and campaign multitape model. The counter algorithm uses the pinned CrocSwap/integer-mult-bounds source attributed in IntMul_CountedStream. Written by Codex.

import Definitions.Def_IntMul_CountedRouter

namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep)

/-- One extra finite service state writes the actual block separator. -/
abbrev State := CountedStream.State ⊕ Unit

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .inl s =>
    let r := CountedStream.transition s a
    (.inl r.1,r.2)
  | .inr _ =>
    (.inl .emit,fun i => safeStep (a i) (if i=1 then .sep else a i)
      (if i=1 then .right else .stay))

/-- A fixed four-tape, five-symbol, fourteen-state counted service. -/
abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .inl .start
  qHalt := .inl .halt
  start_ne_halt := by decide
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | inl s => exact CountedStream.machine.start_preserved s a i hi
    | inr u =>
      change (safeStep (a i) _ _).1=.start ∧ (safeStep (a i) _ _).2≠Move.left
      by_cases h : i=1
      · subst i
        simp [safeStep,hi]
      · simp [safeStep,hi,h]
  start_only_at_start := by
    intro q a i hi
    cases q with
    | inl s => exact CountedStream.machine.start_only_at_start s a i hi
    | inr u =>
      change (safeStep (a i) _ _).1≠.start
      simp only [safeStep,if_neg hi]
      split <;> simp_all
  halt_fixed := by
    intro a
    change (Sum.inl (CountedStream.transition .halt a).1,(CountedStream.transition .halt a).2)=_
    rw [show CountedStream.transition .halt a=(.halt,fun i => (a i,Move.stay)) from
      CountedStream.machine.halt_fixed a]
  input_readonly := by
    intro q a
    cases q with
    | inl s => exact CountedStream.machine.input_readonly s a
    | inr u =>
      change (safeStep (a 0) (a 0) .stay).1=a 0
      exact congrArg Prod.fst (IntMul.TapeAdder.safe_stay _)

def dispatch (cleanup : Bool) (a : Fin 4 → Sym) : Option (Bool × State) :=
  if cleanup then none
  else if a 0=.zero ∨ a 0=.one then some (false,.inr ())
  else some (true,.inl .resetLeft)

/-- A single fixed twenty-nine-state caller; every separator is a real
transition, and the final partial block restores the saved descriptor. -/
noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Bool false dispatch

def blockSize (y : List Bool) : ℕ := IntMul.val y+1

/-- Exact raw-symbol output prefix with one separator before each positive
multiple of the descriptor-sized block length. There is no trailing separator. -/
noncomputable def packedPrefix (x y : List Bool) (j : ℕ) : List Sym :=
  (List.range (min j x.length)).flatMap fun p =>
    (if 0 < p ∧ p % blockSize y=0 then [Sym.sep] else []) ++
      [machine.bitSym (x.getD p false)]

noncomputable def frame (x y : List Bool) (j : ℕ) (q : Option (Bool × State)) : machine.Cfg where
  state := q
  cells := fun i =>
    if i=0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i=1 then machine.tapeOf (packedPrefix x y j)
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
  head := fun i => if i=0 then j+1 else if i=1 then (packedPrefix x y j).length+1
    else y.length+1

end IntMul.CountedBlockSplitter


