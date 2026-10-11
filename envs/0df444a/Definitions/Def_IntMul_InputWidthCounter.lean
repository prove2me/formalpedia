-- Prove2me | Definitions.Def_IntMul_InputWidthCounter
-- name    : IntMul_InputWidthCounter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:27:17.47499+00:00
-- url     : https://prove2.me/theorems/5a0868d9-8b82-4933-99e6-dfa668e4fbf7
-- title:
--   Actual input-derived binary width counter with charged scans and ripple-increment restarts
-- statement:
--   One fixed three-tape machine starts from the ordinary global initial configuration on binary operands x#y with empty work tapes. It scans the actual input, skips the first operand bit and the separator, and physically increments an unbounded binary counter on work tape 2 once per remaining input bit. Ripple growth, actual marker rewinds, scan dispatches and finite-caller returns are performed by its finite table. The original input is retained read-only and global output is retained empty. Complete correctness, exact terminal frame, descriptor value and linear charged clock are separate theorem obligations.
-- source:
--   Original physical construction of the desired output-width descriptor from the original binary input. No supplied width word, length or head-position oracle. Written by Codex.

import Definitions.Def_IntMul_GrowingCounter
import Definitions.Def_IntMul_FiniteCaller

namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

inductive Reader | open | first | scan deriving DecidableEq
instance : Fintype Reader where
  elems := {.open,.first,.scan}
  complete := by intro q;cases q <;> simp
abbrev State := Option (GrowingCounter.State ⊕ Reader)
def counterState (q : GrowingCounter.State) : State :=
  if q=.halt then none else some (.inl q)
def readerState (q : Reader) : State := some (.inr q)

def transition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := GrowingCounter.machine.δ q a
      (counterState r.1,r.2)
  | some (.inr .open) =>
      (readerState .first,fun i => (a i,if i=0 ∨ i=2 then .right else .stay))
  | some (.inr .first) =>
      if a 0=.zero ∨ a 0=.one then
        (readerState .scan,fun i => (a i,if i=0 then .right else .stay))
      else if a 0=.sep then
        (readerState .first,fun i => (a i,if i=0 then .right else .stay))
      else (none,fun i => (a i,.stay))
  | some (.inr .scan) =>
      if a 0=.zero ∨ a 0=.one then
        (counterState .carry,fun i => (a i,if i=0 then .right else .stay))
      else if a 0=.sep then
        (readerState .scan,fun i => (a i,if i=0 then .right else .stay))
      else (none,fun i => (a i,.stay))

abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := readerState .open
  qHalt := none
  start_ne_halt := Option.some_ne_none _
  k := 3
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | none =>
        change a i=Sym.start ∧ Move.stay≠Move.left
        exact ⟨hi,by decide⟩
    | some s =>
        cases s with
        | inl q => exact GrowingCounter.machine.start_preserved q a i hi
        | inr q =>
            cases q <;> simp only [transition]
            all_goals try split_ifs
            all_goals simp_all
            all_goals try split_ifs
            all_goals simp_all
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some s =>
        cases s with
        | inl q => exact GrowingCounter.machine.start_only_at_start q a i hi
        | inr q =>
            cases q <;> simp only [transition]
            all_goals try split_ifs
            all_goals simp_all
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact GrowingCounter.machine.input_readonly q a
        | inr q =>
            cases q <;> simp only [transition]
            all_goals try split_ifs
            all_goals rfl

/-- The actual boundary return reads the next input symbol. A blank halts;
a bit or separator returns to the physical input scanner. -/
def dispatch (_q : Unit) (a : Fin 3 → Sym) : Option (Unit × State) :=
  if a 0=.blank then none else some ((),readerState .scan)
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Unit () dispatch

def bitCount : List Sym → ℕ
  | [] => 0
  | a::w => (if a=.zero ∨ a=.one then 1 else 0)+bitCount w

def readerFrame (q : Reader) (pre tail : List Sym) (bits : List Bool) : subroutine.Cfg where
  state := readerState q
  cells := fun i => if i=0 then subroutine.tapeOf (pre++tail)
    else if i=2 then subroutine.tapeOf (bits.map subroutine.bitSym) else subroutine.tapeOf []
  head := fun i => if i=0 then pre.length+1 else if i=2 then 1 else 0

def counterBase (pre tail : List Sym) (bits : List Bool) : GrowingCounter.machine.Cfg where
  state := .halt
  cells := (readerFrame .scan pre tail bits).cells
  head := (readerFrame .scan pre tail bits).head

def counterView (c : GrowingCounter.machine.Cfg) : subroutine.Cfg where
  state := counterState c.state
  cells := c.cells
  head := c.head

/-- The loop halts immediately at its empty-tail boundary; otherwise its
heads physically name the next bit or separator. -/
def loopFrame (pre tail : List Sym) (bits : List Bool) : machine.Cfg where
  state := if tail=[] then none else some ((),readerState .scan)
  cells := (readerFrame .scan pre tail bits).cells
  head := (readerFrame .scan pre tail bits).head

/-- True global initial configuration on x#y; no width descriptor or counter
bits have been supplied in advance. -/
noncomputable def initialFrame (x y : List Bool) : machine.Cfg := machine.initCfg x y

noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=2 then machine.tapeOf ((GrowingCounter.iterateCounter (x.length+y.length-1) []).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i=0 then x.length+y.length+2 else if i=2 then 1 else 0

end IntMul.InputWidthCounter


