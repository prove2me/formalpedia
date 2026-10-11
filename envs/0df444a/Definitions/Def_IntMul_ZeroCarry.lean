-- Prove2me | Definitions.Def_IntMul_ZeroCarry
-- name    : IntMul_ZeroCarry
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:38:53.880244+00:00
-- url     : https://prove2.me/theorems/56c4ff07-921d-4109-ae9f-673e7f90a6c3
-- title:
--   Complete physical zero carry initialization with actual marker rewind
-- statement:
--   A fixed four-tape finite caller first executes actual binary-counted zero-word generation from prepared countdown/templates, then physically rewinds the generated output to its actual start marker. No zero payload or output cursor jump is supplied. The original input cells and head and both restored countdown/template banks are retained. Full correctness, canonical zero carry and actual transition clock are separate theorem obligations.
-- source:
--   Original complete physical zero carry initialization with a charged real-marker rewind. Written by Codex.

import Definitions.Def_IntMul_CountedZero
import Definitions.Def_IntMul_FiniteCaller
namespace IntMul.ZeroCarry
open TapeCopy (Sym)
abbrev State := Option (CountedZero.State ⊕ Unit)
def zeroState (q : CountedZero.State) : State := if q=.halt then none else some (.inl q)
def rewindState : State := some (.inr ())
def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CountedZero.machine.δ q a
      (zeroState r.1,r.2)
  | some (.inr _) =>
      if a 1=.start then (none,fun i => (a i,.stay))
      else (rewindState,fun i => (a i,if i=1 then .left else .stay))
noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := zeroState .start
  qHalt := none
  start_ne_halt := by decide
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | none =>
        change a i=Sym.start ∧ Move.stay≠Move.left
        exact ⟨hi,by decide⟩
    | some q =>
        cases q with
        | inl q => exact CountedZero.machine.start_preserved q a i hi
        | inr u =>
            change ((if a 1=Sym.start then (none,fun i => (a i,Move.stay))
              else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay))).2 i).1=Sym.start ∧
              ((if a 1=Sym.start then (none,fun i => (a i,Move.stay))
              else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay))).2 i).2≠Move.left
            split_ifs <;> simp_all
            all_goals intro h;subst i;contradiction
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some q =>
        cases q with
        | inl q => exact CountedZero.machine.start_only_at_start q a i hi
        | inr u =>
            change ((if a 1=Sym.start then (none,fun i => (a i,Move.stay))
              else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay))).2 i).1≠Sym.start
            split_ifs <;> exact hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some q =>
        cases q with
        | inl q => exact CountedZero.machine.input_readonly q a
        | inr u =>
            change ((if a 1=Sym.start then (none,fun i => (a i,Move.stay))
              else (rewindState,fun i => (a i,if i=1 then Move.left else Move.stay))).2 0).1=a 0
            split_ifs <;> rfl

def dispatch (rewind : Bool) (_a : Fin 4 → Sym) : Option (Bool × State) :=
  if rewind then none else some (true,rewindState)
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Bool false dispatch
noncomputable def nativeBase (base : machine.Cfg) : CountedZero.machine.Cfg where
  state := .halt
  cells := base.cells
  head := base.head
noncomputable def zeroView (c : CountedZero.machine.Cfg) : subroutine.Cfg where
  state := zeroState c.state
  cells := c.cells
  head := c.head
noncomputable def initialFrame (base : machine.Cfg) (z : List Bool) : machine.Cfg :=
  FiniteCaller.embed subroutine Bool false false dispatch (zeroView (CountedZero.initialFrame (nativeBase base) z))
noncomputable def rewindFrame (base : machine.Cfg) (z : List Bool) (p : ℕ) : subroutine.Cfg where
  state := rewindState
  cells := (CountedZero.finalFrame (nativeBase base) z).cells
  head := Function.update (CountedZero.finalFrame (nativeBase base) z).head 1 p
noncomputable def rewindDone (base : machine.Cfg) (z : List Bool) : subroutine.Cfg :=
  {rewindFrame base z 0 with state := none}
noncomputable def finalFrame (base : machine.Cfg) (z : List Bool) : machine.Cfg where
  state := none
  cells := (CountedZero.finalFrame (nativeBase base) z).cells
  head := Function.update (CountedZero.finalFrame (nativeBase base) z).head 1 0
end IntMul.ZeroCarry


