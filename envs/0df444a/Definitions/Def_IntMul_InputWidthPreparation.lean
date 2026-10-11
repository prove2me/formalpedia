-- Prove2me | Definitions.Def_IntMul_InputWidthPreparation
-- name    : IntMul_InputWidthPreparation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:55:23.186101+00:00
-- url     : https://prove2.me/theorems/3dec550d-56ff-4eb8-9607-85ddd68ad710
-- title:
--   Physical input-derived retained width descriptor and paired countdown initialization
-- statement:
--   A fixed sixteen-tape machine starts from the ordinary initial configuration on binary operands x#y. It computes the desired output-width-minus-one descriptor directly from the original input on retained work tape 15, physically rewinds it to its start marker, and writes its two delimited countdown copies on banks 3 and 4. The original input is read-only, global output remains empty, the retained descriptor is rewound, and both countdown heads reach their least-significant-bit cursors. No width word or counter contents are supplied in advance. Full correctness, exact terminal frame, descriptor value and linear actual clock are separate theorem obligations.
-- source:
--   Original complete physical preparation of retained width and paired countdown banks from true global initialization. Written by Codex.

import Definitions.Def_IntMul_CanonicalWidthDescriptor
import Definitions.Def_IntMul_WidthPreparation

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.InputWidthPreparation
open TapeCopy (Sym)

abbrev State := Option (CanonicalWidthDescriptor.machine.K ⊕ (WidthPreparation.State ⊕ Unit))
noncomputable def computeState (q : CanonicalWidthDescriptor.machine.K) : State :=
  if q=none then none else some (.inl q)
def prepareState (q : WidthPreparation.State) : State :=
  if q=.halt then none else some (.inr (.inl q))
def rewindState : State := some (.inr (.inr ()))

def computeTape (j : Fin 15) : Fin 16 := if j=1 then 15 else ⟨j.val,by have := j.isLt;omega⟩
def computeIndex (i : Fin 16) (hi : i.val<15) : Fin 15 := ⟨i.val,hi⟩
def computeAction (a : Fin 16 → Sym) (r : Fin 15 → Sym × Move) : Fin 16 → Sym × Move :=
  fun i => if i=15 then r 1 else if i=1 then (a i,.stay)
    else if h : i.val<15 then r (computeIndex i h) else (a i,.stay)

noncomputable def transition (q : State) (a : Fin 16 → Sym) : State × (Fin 16 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CanonicalWidthDescriptor.machine.δ q (fun j => a (computeTape j))
      (computeState r.1,computeAction a r.2)
  | some (.inr (.inl q)) =>
      let r := WidthPreparation.machine.δ q a
      (prepareState r.1,r.2)
  | some (.inr (.inr _)) =>
      if a 15=.start then (none,fun i => (a i,.stay))
      else (rewindState,fun i => (a i,if i=15 then .left else .stay))

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := computeState CanonicalWidthDescriptor.machine.qStart
  qHalt := none
  start_ne_halt := by
    have h : CanonicalWidthDescriptor.machine.qStart≠none := CanonicalWidthDescriptor.machine.start_ne_halt
    simp only [computeState,if_neg h]
    exact Option.some_ne_none _
  k := 16
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
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 0 hi
            · change a _=Sym.start ∧ Move.stay≠Move.left
              exact ⟨hi,by decide⟩
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 2 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 3 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 4 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 5 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 6 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 7 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 8 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 9 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 10 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 11 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 12 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 13 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 14 hi
            · exact CanonicalWidthDescriptor.machine.start_preserved q (fun j => a (computeTape j)) 1 hi
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.start_preserved q a i hi
            | inr _ =>
                simp only [transition]
                split_ifs <;> simp_all
                all_goals intro he;subst i;contradiction
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some s =>
        cases s with
        | inl q =>
            fin_cases i
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 0 hi
            · exact hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 2 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 3 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 4 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 5 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 6 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 7 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 8 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 9 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 10 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 11 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 12 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 13 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 14 hi
            · exact CanonicalWidthDescriptor.machine.start_only_at_start q (fun j => a (computeTape j)) 1 hi
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.start_only_at_start q a i hi
            | inr _ => simp [transition];split_ifs <;> exact hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact CanonicalWidthDescriptor.machine.input_readonly q (fun j => a (computeTape j))
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.input_readonly q a
            | inr _ => simp [transition];split_ifs <;> rfl

inductive Phase | compute | rewind | prepare deriving DecidableEq
instance : Fintype Phase where
  elems := {.compute,.rewind,.prepare}
  complete := by intro q;cases q <;> simp
noncomputable def dispatch (q : Phase) (_a : Fin 16 → Sym) : Option (Phase × State) :=
  match q with
  | .compute => some (.rewind,rewindState)
  | .rewind => some (.prepare,prepareState .advance)
  | .prepare => none
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .compute dispatch

noncomputable def initialFrame (x y : List Bool) : machine.Cfg := machine.initCfg x y
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=15 then machine.tapeOf ((CanonicalWidthDescriptor.descriptorWord x y).map machine.bitSym)
    else if i=3 ∨ i=4 then WidthPreparation.descriptorTape (CanonicalWidthDescriptor.descriptorWord x y)
    else machine.tapeOf []
  head := fun i => if i=0 then x.length+y.length+2
    else if i=3 ∨ i=4 then (CanonicalWidthDescriptor.descriptorWord x y).length+1 else 0

end IntMul.InputWidthPreparation


