-- Prove2me | Definitions.Def_IntMul_PaddedCarryStep
-- name    : IntMul_PaddedCarryStep
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T10:29:45.083807+00:00
-- url     : https://prove2.me/theorems/775050e7-2084-478a-914f-71f9db195603
-- title:
--   Fixed ten-tape canonical carry continuation machine
-- statement:
--   The fixed ten-tape local machine performs the accepted physical carry update, generates val(z) literal padding zeroes through an actual binary countdown, then copies the little-endian outgoing carry backwards after those zeroes. The resulting bank is a canonical n-bit next carry operand. The original digit, input and arithmetic banks are retained. The incoming frame explicitly includes a descriptor bank already physically prepared by the caller. The transition table reads only finite state and scanned symbols; its zero generator uses a literal zero symbol and discards the virtual input action. It does not read an oracle tape. Correctness and all actual transition bounds are separate proof obligations.
-- source:
--   Original physical fixed-width outgoing-carry preparation in the integer multiplication multitape model. Written by Codex.

import Definitions.Def_IntMul_CarryStep

namespace IntMul.PaddedCarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive CopyState
  | openPad | turnCarry | reverseCarry
  deriving DecidableEq

instance : Fintype CopyState where
  elems := {.openPad,.turnCarry,.reverseCarry}
  complete := by intro q;cases q <;> simp

abbrev State := Option (CarryStep.machine.K ⊕ (CountedStream.State ⊕ CopyState))

noncomputable def mainState (q : CarryStep.machine.K) : State :=
  if q=none then none else some (.inl q)

def zeroState (q : CountedStream.State) : State :=
  if q=.halt then none else some (.inr (.inl q))

def copyState (q : CopyState) : State := some (.inr (.inr q))

def mainTape (i : Fin 9) : Fin 10 := ⟨i.val,Nat.lt_trans i.isLt (by decide : 9 < 10)⟩

def zeroSymbols (a : Fin 10 → Sym) : Fin 4 → Sym :=
  fun i => if i=0 then .zero else if i=1 then a 9 else if i=2 then a 6 else a 7

def mainAction (a : Fin 10 → Sym) (r : Fin 9 → Sym × Move) : Fin 10 → Sym × Move :=
  fun i => if h : i.val < 9 then r ⟨i.val,h⟩ else (a i,.stay)

def zeroAction (a : Fin 10 → Sym) (r : Fin 4 → Sym × Move) : Fin 10 → Sym × Move :=
  fun i => if i=6 then r 2 else if i=7 then r 3 else if i=9 then r 1 else (a i,.stay)

def copyRaw (q : CopyState) (a : Fin 10 → Sym) : State × (Fin 10 → Sym × Move) :=
  match q with
  | .openPad => (zeroState .carry,fun i => (a i,if i=9 then .right else .stay))
  | .turnCarry => (copyState .reverseCarry,fun i => (a i,if i=8 then .left else .stay))
  | .reverseCarry =>
      if a 8=.zero ∨ a 8=.one then
        (copyState .reverseCarry,fun i => (if i=9 then a 8 else a i,
          if i=8 then .left else if i=9 then .right else .stay))
      else (none,fun i => (a i,.stay))

noncomputable def rawTransition (q : State) (a : Fin 10 → Sym) : State × (Fin 10 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CarryStep.machine.δ q (fun i => a (mainTape i))
      (mainState r.1,mainAction a r.2)
  | some (.inr (.inl q)) =>
      let r := CountedStream.machine.δ q (zeroSymbols a)
      (zeroState r.1,zeroAction a r.2)
  | some (.inr (.inr q)) => copyRaw q a

noncomputable def transition (q : State) (a : Fin 10 → Sym) : State × (Fin 10 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem safe_input (s : Sym) (d : Move) : (safeStep s s d).1=s := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem raw_input (q : State) (a : Fin 10 → Sym) :
    ((rawTransition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some s =>
    cases s with
    | inl q =>
      simpa [rawTransition,mainAction,mainTape,MultitapeTM.inTape] using
        CarryStep.machine.input_readonly q (fun i => a (mainTape i))
    | inr s =>
      cases s with
      | inl q => rfl
      | inr q =>
        cases q <;> simp only [rawTransition,copyRaw]
        all_goals try split_ifs
        all_goals simp

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := some (.inl CarryStep.machine.qStart)
  qHalt := none
  start_ne_halt := by decide
  k := 10
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
  halt_fixed := by intro a;simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1=a 0
    rw [raw_input]
    exact safe_input _ _

inductive Phase
  | main | zeros | reverse
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.main,.zeros,.reverse}
  complete := by intro q;cases q <;> simp

def dispatch (phase : Phase) (_a : Fin 10 → Sym) : Option (Phase × State) :=
  match phase with
  | .main => some (.zeros,copyState .openPad)
  | .zeros => some (.reverse,copyState .turnCarry)
  | .reverse => none

noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine subroutine Phase .main dispatch

def paddingWord (x y z : List Bool) : List Bool :=
  List.replicate (val z) false++(CarryStep.carryWord x y z).reverse

def nextCarryWord (x y z : List Bool) : List Bool :=
  bin x.length ((val x+val y)/(2^CarryStep.blockSize z))

/-- Same incoming local arithmetic frame, with one additional blank output
bank for the next fixed-width carry operand. -/
noncomputable def initialFrame (x y z : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := fun i => if h : i.val < 9 then (CarryStep.initialFrame x y z).cells ⟨i.val,h⟩
    else machine.tapeOf []
  head := fun _ => 0

/-- The low digit is retained, and tape 9 contains the exact canonical n-bit
outgoing carry. The reverse-read carry head is returned to its start marker. -/
noncomputable def finalFrame (x y z : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if h : i.val < 9 then (CarryStep.finalFrame x y z).cells ⟨i.val,h⟩
    else machine.tapeOf ((nextCarryWord x y z).map machine.bitSym)
  head := fun i => if i=8 then 0 else if h : i.val < 9 then (CarryStep.finalFrame x y z).head ⟨i.val,h⟩
    else x.length+1

end IntMul.PaddedCarryStep


