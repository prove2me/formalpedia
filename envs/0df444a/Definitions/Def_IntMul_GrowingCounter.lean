-- Prove2me | Definitions.Def_IntMul_GrowingCounter
-- name    : IntMul_GrowingCounter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:15:25.676514+00:00
-- url     : https://prove2.me/theorems/87d0c397-1981-416b-9773-e921bd980c18
-- title:
--   Actual variable-width binary ripple increment with blank growth and marker rewind
-- statement:
--   One fixed three-tape, five-symbol machine increments a finite little-endian binary word on work bank 2, physically extending it into its actual blank when carry overflows, then seeks its real start marker and returns to the first payload cursor. The input and output caller banks and their heads are retained. The supplied counter word may have arbitrary finite width, including the empty zero word. Mathematical increment, exact terminal frame, exact per-call clock and an amortized linear bound are separate theorem obligations.
-- source:
--   Original physical unbounded binary counter for input-derived width descriptors. Finite control has no width or position oracle. Written by Codex.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.GrowingCounter
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive State | carry | rewind | halt deriving DecidableEq
instance : Fintype State where
  elems := {.carry,.rewind,.halt}
  complete := by intro q;cases q <;> simp

/-- A variable-width little-endian increment on the real work bank 2. Ripple
carry may extend into the actual blank; return seeks the real start marker. -/
def rawTransition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  match q with
  | .carry =>
      if a 2=.one then (.carry,fun i => (if i=2 then .zero else a i,if i=2 then .right else .stay))
      else (.rewind,fun i => (if i=2 then .one else a i,if i=2 then .left else .stay))
  | .rewind =>
      if a 2=.start then (.halt,fun i => (a i,if i=2 then .right else .stay))
      else (.rewind,fun i => (a i,if i=2 then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

def transition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  let r := rawTransition q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .carry
  qHalt := .halt
  start_ne_halt := by decide
  k := 3
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
    have h : ((rawTransition q a).2 0).1=a 0 := by
      cases q <;> simp only [rawTransition]
      all_goals try split_ifs
      all_goals simp_all
    change (safeStep (a 0) ((rawTransition q a).2 0).1 _).1=a 0
    rw [h]
    by_cases hs : a 0=Sym.start <;> simp [safeStep,hs]

def carryLength : List Bool → ℕ
  | [] => 0
  | false::bs => 0
  | true::bs => carryLength bs+1

def increment : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::increment bs

def potential : List Bool → ℕ
  | [] => 0
  | false::bs => potential bs
  | true::bs => potential bs+1

def counterSteps (bs : List Bool) : ℕ := 2*carryLength bs+2

def iterateCounter : ℕ → List Bool → List Bool
  | 0,bs => bs
  | n+1,bs => iterateCounter n (increment bs)
def totalCounterSteps : ℕ → List Bool → ℕ
  | 0,bs => 0
  | n+1,bs => counterSteps bs+totalCounterSteps n (increment bs)

/-- Other caller cells and heads are retained verbatim. The counter itself
has arbitrary finite width, including an empty zero representation. -/
def counterFrame (base : machine.Cfg) (q : State) (bs : List Bool) : machine.Cfg where
  state := q
  cells := Function.update base.cells 2 (machine.tapeOf (bs.map machine.bitSym))
  head := Function.update base.head 2 1

/-- The processed prefix has already been written as low-order zero bits;
the head is at the next ripple position. All caller data remains explicit. -/
def carryFrame (base : machine.Cfg) (done bits : List Bool) : machine.Cfg where
  state := .carry
  cells := Function.update base.cells 2 (machine.tapeOf ((done++bits).map machine.bitSym))
  head := Function.update base.head 2 (done.length+1)

def rewindFrame (base : machine.Cfg) (bits : List Bool) (pos : ℕ) : machine.Cfg where
  state := .rewind
  cells := Function.update base.cells 2 (machine.tapeOf (bits.map machine.bitSym))
  head := Function.update base.head 2 pos

end IntMul.GrowingCounter


