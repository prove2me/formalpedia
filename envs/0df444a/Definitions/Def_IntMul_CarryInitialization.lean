-- Prove2me | Definitions.Def_IntMul_CarryInitialization
-- name    : IntMul_CarryInitialization
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:55:34.06278+00:00
-- url     : https://prove2.me/theorems/305d5650-3868-443c-b94f-c478c52241ae
-- title:
--   Physical descriptor copying and zero-carry initialization in the arithmetic bank
-- statement:
--   A fixed sixteen-tape finite controller starts with a retained precision descriptor l on tape 15 at its marker, empty countdown/template tapes 3 and 4, and an empty carry bank 12. It physically prepares both marked descriptor copies, generates val(l)+1 zero bits directly into bank 12, and rewinds that bank head to its marker. Original input and all other caller banks and heads are retained. Full exact-frame correctness and the charged clock are separate theorem obligations.
-- source:
--   Original charged physical descriptor-to-carry preparation controller. Written by Codex.

import Definitions.Def_IntMul_WidthPreparation
import Definitions.Def_IntMul_ZeroCarry
namespace IntMul.CarryInitialization
open TapeCopy (Sym)
abbrev State := Option (WidthPreparation.State ⊕ ZeroCarry.machine.K)
def widthState (q : WidthPreparation.State) : State := if q=.halt then none else some (.inl q)
noncomputable def zeroState (q : ZeroCarry.machine.K) : State := by
  classical
  exact if q=ZeroCarry.machine.qHalt then none else some (.inr q)
def zeroTape (j : Fin 4) : Fin 16 := if j.val=0 then 0 else if j.val=1 then 12 else if j.val=2 then 3 else 4
def zeroAction (a : Fin 16 → Sym) (r : Fin 4 → Sym × Move) (i : Fin 16) : Sym × Move :=
  if i.val=0 then r 0 else if i.val=12 then r 1 else if i.val=3 then r 2 else if i.val=4 then r 3 else (a i,.stay)
noncomputable def transition (q : State) (a : Fin 16 → Sym) : State × (Fin 16 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) => let r := WidthPreparation.machine.δ q a;(widthState r.1,r.2)
  | some (.inr q) => let r := ZeroCarry.machine.δ q (fun j => a (zeroTape j));(zeroState r.1,zeroAction a r.2)
noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := widthState .advance
  qHalt := none
  start_ne_halt := by decide
  k := 16
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
        | inl q => exact WidthPreparation.machine.start_preserved q a i hi
        | inr q =>
            fin_cases i
            all_goals first
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_preserved q (fun j => a (zeroTape j)) 0 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_preserved q (fun j => a (zeroTape j)) 1 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_preserved q (fun j => a (zeroTape j)) 2 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_preserved q (fun j => a (zeroTape j)) 3 hi)
              | (simpa [transition,zeroAction] using And.intro hi (by decide : Move.stay≠Move.left))
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some q =>
        cases q with
        | inl q => exact WidthPreparation.machine.start_only_at_start q a i hi
        | inr q =>
            fin_cases i
            all_goals first
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_only_at_start q (fun j => a (zeroTape j)) 0 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_only_at_start q (fun j => a (zeroTape j)) 1 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_only_at_start q (fun j => a (zeroTape j)) 2 hi)
              | (simpa [transition,zeroAction,zeroTape] using
                  ZeroCarry.machine.start_only_at_start q (fun j => a (zeroTape j)) 3 hi)
              | (simpa [transition,zeroAction] using hi)
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some q =>
        cases q with
        | inl q => exact WidthPreparation.machine.input_readonly q a
        | inr q => simpa [transition,zeroAction,zeroTape] using
            ZeroCarry.machine.input_readonly q (fun j => a (zeroTape j))
noncomputable def dispatch (zero : Bool) (_a : Fin 16 → Sym) : Option (Bool × State) :=
  if zero then none else some (true,zeroState ZeroCarry.machine.qStart)
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Bool false dispatch
noncomputable def widthBase (base : machine.Cfg) : WidthPreparation.machine.Cfg where
  state := .halt
  cells := Function.update base.cells 12 (WidthPreparation.machine.tapeOf [])
  head := Function.update base.head 12 0
noncomputable def widthView (c : WidthPreparation.machine.Cfg) : subroutine.Cfg where
  state := widthState c.state
  cells := c.cells
  head := c.head
noncomputable def zeroBase (base : machine.Cfg) (l : List Bool) : ZeroCarry.machine.Cfg where
  state := ZeroCarry.machine.qHalt
  cells := fun j => (WidthPreparation.finalFrame (widthBase base) l).cells (zeroTape j)
  head := fun j => (WidthPreparation.finalFrame (widthBase base) l).head (zeroTape j)
noncomputable def zeroView (base : machine.Cfg) (l : List Bool) (c : ZeroCarry.machine.Cfg) : subroutine.Cfg where
  state := zeroState c.state
  cells := fun i => if i.val=0 then c.cells 0 else if i.val=12 then c.cells 1 else if i.val=3 then c.cells 2
    else if i.val=4 then c.cells 3 else (WidthPreparation.finalFrame (widthBase base) l).cells i
  head := fun i => if i.val=0 then c.head 0 else if i.val=12 then c.head 1 else if i.val=3 then c.head 2
    else if i.val=4 then c.head 3 else (WidthPreparation.finalFrame (widthBase base) l).head i
noncomputable def initialFrame (base : machine.Cfg) (l : List Bool) : machine.Cfg :=
  FiniteCaller.embed subroutine Bool false false dispatch
    (widthView (WidthPreparation.initialFrame (widthBase base) l))
noncomputable def finalFrame (base : machine.Cfg) (l : List Bool) : machine.Cfg where
  state := machine.qHalt
  cells := Function.update (WidthPreparation.finalFrame (widthBase base) l).cells 12
    (machine.tapeOf ((bin (val l+1) 0).map machine.bitSym))
  head := (WidthPreparation.finalFrame (widthBase base) l).head
end IntMul.CarryInitialization


