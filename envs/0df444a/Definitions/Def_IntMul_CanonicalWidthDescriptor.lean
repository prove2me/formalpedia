-- Prove2me | Definitions.Def_IntMul_CanonicalWidthDescriptor
-- name    : IntMul_CanonicalWidthDescriptor
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:46:09.500169+00:00
-- url     : https://prove2.me/theorems/1e4e4bdd-7feb-4455-a8fb-2607fa6245a9
-- title:
--   Actual input-derived canonical output-width descriptor from global initialization
-- statement:
--   One fixed fifteen-tape machine starts from the true global initial configuration on x#y. It physically counts operand bits with a growing little-endian counter, seeks its actual terminating blank and physically reverses that counter into the big-endian output-width-minus-one descriptor. Every original input cell is retained, all scratch banks are empty at completion, and all seeks, reversals, erasures and caller returns are actual transitions. No descriptor, length or head-position oracle is supplied. Complete correctness, value and linear clock are separate theorem obligations.
-- source:
--   Original complete physical width descriptor preparation from operand input. Written by Codex.

import Definitions.Def_IntMul_InputWidthCounter
import Definitions.Def_IntMul_CanonicalOutput

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CanonicalWidthDescriptor
open TapeCopy (Sym)

abbrev State := Option (InputWidthCounter.machine.K ⊕ (CanonicalOutput.machine.K ⊕ Unit))
noncomputable def countState (q : InputWidthCounter.machine.K) : State :=
  if q=none then none else some (.inl q)
noncomputable def orderState (q : CanonicalOutput.machine.K) : State :=
  if q=none then none else some (.inr (.inl q))
def seekState : State := some (.inr (.inr ()))

def countTape (j : Fin 3) : Fin 15 := if j=0 then 0 else if j=1 then 3 else 1
def countAction (a : Fin 15 → Sym) (r : Fin 3 → Sym × Move) : Fin 15 → Sym × Move :=
  fun i => if i=0 then r 0 else if i=1 then r 2 else if i=3 then r 1 else (a i,.stay)

/-- Literal physical counter execution, actual seek to its terminating blank,
and literal physical reversal. Input heads and length are never read as data. -/
noncomputable def transition (q : State) (a : Fin 15 → Sym) : State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := InputWidthCounter.machine.δ q (fun j => a (countTape j))
      (countState r.1,countAction a r.2)
  | some (.inr (.inl q)) =>
      let r := CanonicalOutput.machine.δ q a
      (orderState r.1,r.2)
  | some (.inr (.inr _)) =>
      if a 1=.blank then (none,fun i => (a i,.stay))
      else (seekState,fun i => (a i,if i=1 then .right else .stay))

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := countState InputWidthCounter.machine.qStart
  qHalt := none
  start_ne_halt := by
    have h : InputWidthCounter.machine.qStart≠none := InputWidthCounter.machine.start_ne_halt
    simp only [countState,if_neg h]
    exact Option.some_ne_none _
  k := 15
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
        | inl q =>
            fin_cases i
            · exact InputWidthCounter.machine.start_preserved q (fun j => a (countTape j)) 0 hi
            · exact InputWidthCounter.machine.start_preserved q (fun j => a (countTape j)) 2 hi
            · change a _=Sym.start ∧ Move.stay≠Move.left
              exact ⟨hi,by decide⟩
            · exact InputWidthCounter.machine.start_preserved q (fun j => a (countTape j)) 1 hi
            all_goals
              change a _=Sym.start ∧ Move.stay≠Move.left
              exact ⟨hi,by decide⟩
        | inr s =>
            cases s with
            | inl q => exact CanonicalOutput.machine.start_preserved q a i hi
            | inr _ =>
                simp only [transition]
                split_ifs <;> simp_all
                all_goals split_ifs <;> simp_all
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some s =>
        cases s with
        | inl q =>
            fin_cases i
            · exact InputWidthCounter.machine.start_only_at_start q (fun j => a (countTape j)) 0 hi
            · exact InputWidthCounter.machine.start_only_at_start q (fun j => a (countTape j)) 2 hi
            · exact hi
            · exact InputWidthCounter.machine.start_only_at_start q (fun j => a (countTape j)) 1 hi
            all_goals exact hi
        | inr s =>
            cases s with
            | inl q => exact CanonicalOutput.machine.start_only_at_start q a i hi
            | inr _ => simp [transition];split_ifs <;> exact hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact InputWidthCounter.machine.input_readonly q (fun j => a (countTape j))
        | inr s =>
            cases s with
            | inl q => exact CanonicalOutput.machine.input_readonly q a
            | inr _ => simp [transition];split_ifs <;> rfl

inductive Phase | count | seek | order deriving DecidableEq
instance : Fintype Phase where
  elems := {.count,.seek,.order}
  complete := by intro q;cases q <;> simp
noncomputable def dispatch (q : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match q with
  | .count => some (.seek,seekState)
  | .seek => some (.order,orderState CanonicalOutput.machine.qStart)
  | .order => none
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .count dispatch

def descriptorWord (x y : List Bool) : List Bool :=
  (GrowingCounter.iterateCounter (x.length+y.length-1) []).reverse
noncomputable def initialFrame (x y : List Bool) : machine.Cfg := machine.initCfg x y
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=1 then machine.tapeOf ((descriptorWord x y).map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=0 then x.length+y.length+2 else if i=1 then (descriptorWord x y).length+1 else 0

end IntMul.CanonicalWidthDescriptor


