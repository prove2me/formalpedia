-- Prove2me | Definitions.Def_IntMul_ReversedBlockRouter
-- name    : IntMul_ReversedBlockRouter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T09:29:44.066383+00:00
-- url     : https://prove2.me/theorems/8d0da16f-f722-45f0-a815-29d0ef9f4cad
-- title:
--   Actual six-tape reversal, request routing and descriptor-sized block splitting machine
-- statement:
--   One fixed six-tape multitape Turing machine first reverses its binary operand, physically copies the reversed word and descriptor into a scratch request, rewinds that request to its start marker, and runs the descriptor-sized block splitter. It uses the original read-only input, output, reverse scratch, splitter input scratch, counter and saved-template tapes. A three-phase finite caller charges every subroutine return. The complete final frame records exact separated output and all six tape contents and head positions. Blocks are ordered from least significant to most significant, with little-endian bits within each block. No coordinate, length, reset or copying oracle is supplied to the finite transition table; correctness and total clock are separate obligations.
-- source:
--   Original complete physical digit-routing composition in the campaign multitape model. Written by Codex.

import Definitions.Def_IntMul_TapeReverse
import Definitions.Def_IntMul_CountedBlockSplitter

namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive Relay
  | align | copyReverse | copyDescriptor | rewind
  deriving DecidableEq

instance : Fintype Relay where
  elems := {.align,.copyReverse,.copyDescriptor,.rewind}
  complete := by intro q; cases q <;> simp

abbrev State := Option (TapeReverse.State ⊕ (Relay ⊕ CountedBlockSplitter.machine.K))

def reverseState (q : TapeReverse.State) : State :=
  if q=.halt then none else some (.inl q)

def splitState (q : CountedBlockSplitter.machine.K) : State :=
  if q=none then none else some (.inr (.inr q))

def relayState (q : Relay) : State := some (.inr (.inl q))

def reverseTape (i : Fin 2) : Fin 6 := if i=0 then 0 else 2

def splitTape (i : Fin 4) : Fin 6 :=
  if i=0 then 3 else if i=1 then 1 else if i=2 then 4 else 5

def reverseAction (a : Fin 6 → Sym) (r : Fin 2 → Sym × Move) : Fin 6 → Sym × Move :=
  fun i => if i=0 then r 0 else if i=2 then r 1 else (a i,.stay)

def splitAction (a : Fin 6 → Sym) (r : Fin 4 → Sym × Move) : Fin 6 → Sym × Move :=
  fun i => if i=1 then r 1 else if i=3 then r 0 else if i=4 then r 2
    else if i=5 then r 3 else (a i,.stay)

def relayRaw (q : Relay) (a : Fin 6 → Sym) : State × (Fin 6 → Sym × Move) :=
  match q with
  | .align =>
      if a 0=.sep ∧ a 2=.start then
        (relayState .copyReverse,fun i => (a i,if i=2 ∨ i=3 then .right else .stay))
      else (relayState .align,fun i => (a i,if i=0 then .right else if i=2 then .left else .stay))
  | .copyReverse =>
      if a 2=.zero ∨ a 2=.one then
        (relayState .copyReverse,fun i => (if i=3 then a 2 else a i,
          if i=2 ∨ i=3 then .right else .stay))
      else (relayState .copyDescriptor,fun i => (if i=3 then .sep else a i,
        if i=0 ∨ i=3 then .right else .stay))
  | .copyDescriptor =>
      if a 0=.zero ∨ a 0=.one then
        (relayState .copyDescriptor,fun i => (if i=3 then a 0 else a i,
          if i=0 ∨ i=3 then .right else .stay))
      else (relayState .rewind,fun i => (a i,if i=3 then .left else .stay))
  | .rewind =>
      if a 3=.start then (none,fun i => (a i,.stay))
      else (relayState .rewind,fun i => (a i,if i=3 then .left else .stay))

noncomputable def rawTransition (q : State) (a : Fin 6 → Sym) : State × (Fin 6 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := TapeReverse.machine.δ q (fun i => a (reverseTape i))
      (reverseState r.1,reverseAction a r.2)
  | some (.inr (.inl q)) => relayRaw q a
  | some (.inr (.inr q)) =>
      let r := CountedBlockSplitter.machine.δ q (fun i => a (splitTape i))
      (splitState r.1,splitAction a r.2)

noncomputable def transition (q : State) (a : Fin 6 → Sym) : State × (Fin 6 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem safe_input (s : Sym) (d : Move) : (safeStep s s d).1=s := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem raw_input (q : State) (a : Fin 6 → Sym) :
    ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl q =>
      simpa [rawTransition,reverseAction,reverseTape,MultitapeTM.inTape] using
        TapeReverse.machine.input_readonly q (fun i => a (reverseTape i))
    | inr s =>
      cases s with
      | inr q => rfl
      | inl q =>
        cases q <;> simp only [rawTransition,relayRaw]
        all_goals split_ifs <;> simp

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := some (.inl .start)
  qHalt := none
  start_ne_halt := by decide
  k := 6
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1=.start ∧ (safeStep (a i) _ _).2≠Move.left
    simp only [safeStep,hi,if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1≠.start
    simp only [safeStep,if_neg hi]
    split <;> simp_all
  halt_fixed := by
    intro a
    simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1=a 0
    rw [raw_input]
    exact safe_input _ _

inductive Phase
  | reverse | transfer | split
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.reverse,.transfer,.split}
  complete := by intro q; cases q <;> simp

noncomputable def dispatch (phase : Phase) (_a : Fin 6 → Sym) : Option (Phase × State) :=
  match phase with
  | .reverse => some (.transfer,relayState .align)
  | .transfer => some (.split,splitState CountedBlockSplitter.machine.qStart)
  | .split => none

noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Phase .reverse dispatch

/-- Complete actual low-significance-first digit-routing result. The bits
inside each separated block are little-endian. -/
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i =>
    if i=0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i=1 then machine.tapeOf (CountedBlockSplitter.packedPrefix x.reverse y x.length)
    else if i=2 then machine.tapeOf (x.reverse.map machine.bitSym)
    else if i=3 then machine.tapeOf (x.reverse.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
  head := fun i =>
    if i=0 then x.length+y.length+2
    else if i=1 then (CountedBlockSplitter.packedPrefix x.reverse y x.length).length+1
    else if i=2 ∨ i=3 then x.length+1
    else y.length+1

end IntMul.ReversedBlockRouter


