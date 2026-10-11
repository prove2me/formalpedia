-- Prove2me | Definitions.Def_IntMul_InputBlockDescriptors
-- name    : IntMul_InputBlockDescriptors
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T15:12:53.432349+00:00
-- url     : https://prove2.me/theorems/a5c5b3f3-0bd1-40f8-b256-c8e1500170a3
-- title:
--   Actual original-input width and logarithmic block-size descriptor preparation
-- statement:
--   A fixed seventeen-tape machine starts from the ordinary initial configuration on binary operands x#y. It computes the retained total-width-minus-one descriptor and its two countdown copies, physically counts that descriptor to obtain a positive logarithmic block width, canonically reverses the new counter word, and rewinds both retained descriptors to their actual start markers. Original input is read-only, output remains empty, and all temporary banks are cleaned. No numerical length, width or block-size descriptor is supplied in advance. Exact correctness, complete final frame, logarithmic descriptor values and actual clock are separate theorem obligations.
-- source:
--   Original fully charged construction of width and logarithmic block-size descriptors from operand input. Written by Codex.

import Definitions.Def_IntMul_InputWidthPreparation
import Definitions.Def_IntMul_WordWidthCounter

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.InputBlockDescriptors
open TapeCopy (Sym)

inductive Relay | seek | rewind deriving DecidableEq
instance : Fintype Relay where
  elems := {.seek,.rewind}
  complete := by intro q;cases q <;> simp
abbrev State := Option (InputWidthPreparation.machine.K ⊕ (WordWidthCounter.machine.K ⊕ (CanonicalOutput.machine.K ⊕ Relay)))
noncomputable def widthState (q : InputWidthPreparation.machine.K) : State :=
  if q=none then none else some (.inl q)
noncomputable def wordState (q : WordWidthCounter.machine.K) : State :=
  if q=none then none else some (.inr (.inl q))
noncomputable def orderState (q : CanonicalOutput.machine.K) : State :=
  if q=none then none else some (.inr (.inr (.inl q)))
def relayState (q : Relay) : State := some (.inr (.inr (.inr q)))

def widthTape (j : Fin 16) : Fin 17 := ⟨j.val,by have := j.isLt;omega⟩
def widthIndex (i : Fin 17) (hi : i.val<16) : Fin 16 := ⟨i.val,hi⟩
def widthAction (a : Fin 17 → Sym) (r : Fin 16 → Sym × Move) : Fin 17 → Sym × Move :=
  fun i => if h : i.val<16 then r (widthIndex i h) else (a i,.stay)
def wordTape (j : Fin 3) : Fin 17 := if j=0 then 15 else if j=1 then 13 else 16
def wordAction (a : Fin 17 → Sym) (r : Fin 3 → Sym × Move) : Fin 17 → Sym × Move :=
  fun i => if i=15 then r 0 else if i=13 then r 1 else if i=16 then r 2 else (a i,.stay)
def orderTape (j : Fin 15) : Fin 17 := if j=1 then 16 else ⟨j.val,by have := j.isLt;omega⟩
def orderIndex (i : Fin 17) (hi : i.val<15) : Fin 15 := ⟨i.val,hi⟩
def orderAction (a : Fin 17 → Sym) (r : Fin 15 → Sym × Move) : Fin 17 → Sym × Move :=
  fun i => if i=16 then r 1 else if i=1 then (a i,.stay)
    else if h : i.val<15 then r (orderIndex i h) else (a i,.stay)

noncomputable def transition (q : State) (a : Fin 17 → Sym) : State × (Fin 17 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := InputWidthPreparation.machine.δ q (fun j => a (widthTape j))
      (widthState r.1,widthAction a r.2)
  | some (.inr (.inl q)) =>
      let r := WordWidthCounter.machine.δ q (fun j => a (wordTape j))
      (wordState r.1,wordAction a r.2)
  | some (.inr (.inr (.inl q))) =>
      let r := CanonicalOutput.machine.δ q (fun j => a (orderTape j))
      (orderState r.1,orderAction a r.2)
  | some (.inr (.inr (.inr .seek))) =>
      if a 16=.blank then (none,fun i => (a i,.stay))
      else (relayState .seek,fun i => (a i,if i=16 then .right else .stay))
  | some (.inr (.inr (.inr .rewind))) =>
      if a 15=.start ∧ a 16=.start then (none,fun i => (a i,.stay))
      else (relayState .rewind,fun i => (a i,
        if (i=15 ∨ i=16) ∧ a i≠.start then .left else .stay))

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := widthState InputWidthPreparation.machine.qStart
  qHalt := none
  start_ne_halt := by
    have h : InputWidthPreparation.machine.qStart≠none := InputWidthPreparation.machine.start_ne_halt
    simp only [widthState,if_neg h]
    exact Option.some_ne_none _
  k := 17
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
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 0 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 1 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 2 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 3 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 4 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 5 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 6 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 7 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 8 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 9 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 10 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 11 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 12 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 13 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 14 hi
            · exact InputWidthPreparation.machine.start_preserved q (fun j => a (widthTape j)) 15 hi
            · change a _=Sym.start ∧ Move.stay≠Move.left
              exact ⟨hi,by decide⟩
        | inr s =>
            cases s with
            | inl q =>
                fin_cases i
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · exact WordWidthCounter.machine.start_preserved q (fun j => a (wordTape j)) 1 hi
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · exact WordWidthCounter.machine.start_preserved q (fun j => a (wordTape j)) 0 hi
                · exact WordWidthCounter.machine.start_preserved q (fun j => a (wordTape j)) 2 hi
            | inr s =>
                cases s with
                | inl q =>
                    fin_cases i
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 0 hi
                    · change a _=Sym.start ∧ Move.stay≠Move.left
                      exact ⟨hi,by decide⟩
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 2 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 3 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 4 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 5 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 6 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 7 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 8 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 9 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 10 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 11 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 12 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 13 hi
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 14 hi
                    · change a _=Sym.start ∧ Move.stay≠Move.left
                      exact ⟨hi,by decide⟩
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 1 hi
                | inr q =>
                    cases q <;> simp only [transition]
                    all_goals split_ifs <;> simp_all
                    all_goals try split_ifs <;> simp_all
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none =>
        exact hi
    | some s =>
        cases s with
        | inl q =>
            fin_cases i
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 0 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 1 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 2 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 3 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 4 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 5 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 6 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 7 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 8 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 9 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 10 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 11 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 12 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 13 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 14 hi
            · exact InputWidthPreparation.machine.start_only_at_start q (fun j => a (widthTape j)) 15 hi
            · exact hi
        | inr s =>
            cases s with
            | inl q =>
                fin_cases i
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact hi
                · exact WordWidthCounter.machine.start_only_at_start q (fun j => a (wordTape j)) 1 hi
                · exact hi
                · exact WordWidthCounter.machine.start_only_at_start q (fun j => a (wordTape j)) 0 hi
                · exact WordWidthCounter.machine.start_only_at_start q (fun j => a (wordTape j)) 2 hi
            | inr s =>
                cases s with
                | inl q =>
                    fin_cases i
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 0 hi
                    · exact hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 2 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 3 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 4 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 5 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 6 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 7 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 8 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 9 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 10 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 11 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 12 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 13 hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 14 hi
                    · exact hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 1 hi
                | inr q =>
                    cases q with
                    | seek =>
                        change ((if a 16=Sym.blank then (none,fun i => (a i,Move.stay))
                          else (relayState .seek,fun i => (a i,if i=16 then Move.right else Move.stay))).2 i).1≠Sym.start
                        split_ifs <;> exact hi
                    | rewind =>
                        change ((if a 15=Sym.start ∧ a 16=Sym.start then (none,fun i => (a i,Move.stay))
                          else (relayState .rewind,fun i => (a i,
                            if (i=15 ∨ i=16) ∧ a i≠Sym.start then Move.left else Move.stay))).2 i).1≠Sym.start
                        split_ifs <;> exact hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact InputWidthPreparation.machine.input_readonly q (fun j => a (widthTape j))
        | inr s =>
            cases s with
            | inl q => rfl
            | inr s =>
                cases s with
                | inl q => exact CanonicalOutput.machine.input_readonly q (fun j => a (orderTape j))
                | inr q =>
                    cases q with
                    | seek =>
                        change ((if a 16=Sym.blank then (none,fun i => (a i,Move.stay))
                          else (relayState .seek,fun i => (a i,if i=16 then Move.right else Move.stay))).2 0).1=a 0
                        split_ifs <;> rfl
                    | rewind =>
                        change ((if a 15=Sym.start ∧ a 16=Sym.start then (none,fun i => (a i,Move.stay))
                          else (relayState .rewind,fun i => (a i,
                            if (i=15 ∨ i=16) ∧ a i≠Sym.start then Move.left else Move.stay))).2 0).1=a 0
                        split_ifs <;> rfl

inductive Phase | width | word | seek | order | rewind deriving DecidableEq
instance : Fintype Phase where
  elems := {.width,.word,.seek,.order,.rewind}
  complete := by intro q;cases q <;> simp
noncomputable def dispatch (q : Phase) (_a : Fin 17 → Sym) : Option (Phase × State) :=
  match q with
  | .width => some (.word,wordState WordWidthCounter.machine.qStart)
  | .word => some (.seek,relayState .seek)
  | .seek => some (.order,orderState CanonicalOutput.machine.qStart)
  | .order => some (.rewind,relayState .rewind)
  | .rewind => none
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .width dispatch

def widthWord (x y : List Bool) := CanonicalWidthDescriptor.descriptorWord x y
def blockWord (x y : List Bool) := (WordWidthCounter.counterWord (widthWord x y)).reverse
noncomputable def initialFrame (x y : List Bool) : machine.Cfg := machine.initCfg x y
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=15 then machine.tapeOf ((widthWord x y).map machine.bitSym)
    else if i=16 then machine.tapeOf ((blockWord x y).map machine.bitSym)
    else if i=3 ∨ i=4 then WidthPreparation.descriptorTape (widthWord x y)
    else machine.tapeOf []
  head := fun i => if i=0 then x.length+y.length+2
    else if i=3 ∨ i=4 then (widthWord x y).length+1 else 0

end IntMul.InputBlockDescriptors


