-- Prove2me | Definitions.Def_IntMul_InputArithmeticDescriptors
-- name    : IntMul_InputArithmeticDescriptors
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T15:57:49.84655+00:00
-- url     : https://prove2.me/theorems/9b727a3c-07a9-4c2f-9bed-3d193aeab099
-- title:
--   Physical input-derived width, logarithmic block and triple-block precision descriptors
-- statement:
--   A fixed eighteen-tape machine starts from the original marked binary operands $x\#y$ and computes three actual retained big-endian parameter words. These represent total input width minus one, positive logarithmic block size minus one, and triple-block coefficient precision minus one. Its finite phases physically prepare the first two descriptors, construct the affine precision value, reverse the precision output and rewind it to its real marker. It preserves the original input, leaves global output empty, retains both width countdown copies, and stores all parameter heads at their markers. Correctness and actual transition bounds are separate theorem obligations. No numerical parameter word is supplied by the caller.
-- source:
--   Original physical input-derived arithmetic parameter machine with retained concrete tape frame. Written by Codex.

import Definitions.Def_IntMul_InputBlockDescriptors
import Definitions.Def_IntMul_AffineTriple

set_option maxHeartbeats 1000000
set_option Elab.async false
namespace IntMul.InputArithmeticDescriptors
open TapeCopy (Sym)
inductive Relay | rewind deriving DecidableEq
instance : Fintype Relay where
  elems := {.rewind}
  complete := by intro q;cases q;simp
abbrev State := Option (InputBlockDescriptors.machine.K ⊕ (AffineTriple.machine.K ⊕ (CanonicalOutput.machine.K ⊕ Relay)))
noncomputable def widthState (q : InputBlockDescriptors.machine.K) : State :=
  if q=none then none else some (.inl q)
noncomputable def affineState (q : AffineTriple.machine.K) : State :=
  if q=AffineTriple.State.halt then none else some (.inr (.inl q))
noncomputable def orderState (q : CanonicalOutput.machine.K) : State :=
  if q=none then none else some (.inr (.inr (.inl q)))
def relayState : State := some (.inr (.inr (.inr .rewind)))
def widthTape (j : Fin 17) : Fin 18 := ⟨j.val,by have := j.isLt;omega⟩
def widthIndex (i : Fin 18) (hi : i.val<17) : Fin 17 := ⟨i.val,hi⟩
def widthAction (a : Fin 18 → Sym) (r : Fin 17 → Sym × Move) : Fin 18 → Sym × Move :=
  fun i => if h : i.val<17 then r (widthIndex i h) else (a i,.stay)
def affineTape (j : Fin 3) : Fin 18 := if j=0 then 16 else if j=1 then 17 else 13
def affineAction (a : Fin 18 → Sym) (r : Fin 3 → Sym × Move) : Fin 18 → Sym × Move :=
  fun i => if i=16 then r 0 else if i=17 then r 1 else if i=13 then r 2 else (a i,.stay)
def orderTape (j : Fin 15) : Fin 18 := if j=1 then 17 else ⟨j.val,by have := j.isLt;omega⟩
def orderIndex (i : Fin 18) (hi : i.val<15) : Fin 15 := ⟨i.val,hi⟩
def orderAction (a : Fin 18 → Sym) (r : Fin 15 → Sym × Move) : Fin 18 → Sym × Move :=
  fun i => if i=17 then r 1 else if i=1 then (a i,.stay)
    else if h : i.val<15 then r (orderIndex i h) else (a i,.stay)
noncomputable def transition (q : State) (a : Fin 18 → Sym) : State × (Fin 18 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := InputBlockDescriptors.machine.δ q (fun j => a (widthTape j))
      (widthState r.1,widthAction a r.2)
  | some (.inr (.inl q)) =>
      let r := AffineTriple.machine.δ q (fun j => a (affineTape j))
      (affineState r.1,affineAction a r.2)
  | some (.inr (.inr (.inl q))) =>
      let r := CanonicalOutput.machine.δ q (fun j => a (orderTape j))
      (orderState r.1,orderAction a r.2)
  | some (.inr (.inr (.inr .rewind))) =>
      if a 17=.start then (none,fun i => (a i,.stay))
      else (relayState,fun i => (a i,if i=17 then .left else .stay))
noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := widthState InputBlockDescriptors.machine.qStart
  qHalt := none
  start_ne_halt := by
    have h : InputBlockDescriptors.machine.qStart≠none := InputBlockDescriptors.machine.start_ne_halt
    simp only [widthState,if_neg h]
    exact Option.some_ne_none _
  k := 18
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | none =>
        change a i=Sym.start ∧ Move.stay≠Move.left
        exact ⟨hi,by decide⟩
    | some t =>
        cases t with
        | inl q =>
            fin_cases i
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 0 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 1 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 2 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 3 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 4 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 5 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 6 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 7 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 8 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 9 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 10 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 11 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 12 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 13 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 14 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 15 hi
            · exact InputBlockDescriptors.machine.start_preserved q (fun j => a (widthTape j)) 16 hi
            · change a _=Sym.start ∧ Move.stay≠Move.left
              exact ⟨hi,by decide⟩
        | inr t =>
            cases t with
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
                · exact AffineTriple.machine.start_preserved q (fun j => a (affineTape j)) 2 hi
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · change a _=Sym.start ∧ Move.stay≠Move.left
                  exact ⟨hi,by decide⟩
                · exact AffineTriple.machine.start_preserved q (fun j => a (affineTape j)) 0 hi
                · exact AffineTriple.machine.start_preserved q (fun j => a (affineTape j)) 1 hi
            | inr t =>
                cases t with
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
                    · change a _=Sym.start ∧ Move.stay≠Move.left
                      exact ⟨hi,by decide⟩
                    · exact CanonicalOutput.machine.start_preserved q (fun j => a (orderTape j)) 1 hi
                | inr q =>
                    cases q
                    change ((if a 17=Sym.start then (none,fun i => (a i,Move.stay))
                      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay))).2 i).1=Sym.start ∧ ((if a 17=Sym.start then (none,fun i => (a i,Move.stay))
                      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay))).2 i).2≠Move.left
                    split_ifs <;> simp_all
                    all_goals intro h;subst i;contradiction
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none =>
        exact hi
    | some t =>
        cases t with
        | inl q =>
            fin_cases i
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 0 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 1 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 2 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 3 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 4 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 5 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 6 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 7 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 8 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 9 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 10 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 11 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 12 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 13 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 14 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 15 hi
            · exact InputBlockDescriptors.machine.start_only_at_start q (fun j => a (widthTape j)) 16 hi
            · exact hi
        | inr t =>
            cases t with
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
                · exact AffineTriple.machine.start_only_at_start q (fun j => a (affineTape j)) 2 hi
                · exact hi
                · exact hi
                · exact AffineTriple.machine.start_only_at_start q (fun j => a (affineTape j)) 0 hi
                · exact AffineTriple.machine.start_only_at_start q (fun j => a (affineTape j)) 1 hi
            | inr t =>
                cases t with
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
                    · exact hi
                    · exact CanonicalOutput.machine.start_only_at_start q (fun j => a (orderTape j)) 1 hi
                | inr q =>
                    cases q
                    change ((if a 17=Sym.start then (none,fun i => (a i,Move.stay))
                      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay))).2 i).1≠Sym.start
                    split_ifs <;> exact hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some t =>
        cases t with
        | inl q => exact InputBlockDescriptors.machine.input_readonly q (fun j => a (widthTape j))
        | inr t =>
            cases t with
            | inl q => rfl
            | inr t =>
                cases t with
                | inl q => exact CanonicalOutput.machine.input_readonly q (fun j => a (orderTape j))
                | inr q =>
                    cases q
                    change ((if a 17=Sym.start then (none,fun i => (a i,Move.stay))
                      else (relayState,fun i => (a i,if i=17 then Move.left else Move.stay))).2 0).1=a 0
                    split_ifs <;> rfl
inductive Phase | width | affine | order | rewind deriving DecidableEq
instance : Fintype Phase where
  elems := {.width,.affine,.order,.rewind}
  complete := by intro q;cases q <;> simp
noncomputable def dispatch (q : Phase) (_a : Fin 18 → Sym) : Option (Phase × State) :=
  match q with
  | .width => some (.affine,affineState AffineTriple.machine.qStart)
  | .affine => some (.order,orderState CanonicalOutput.machine.qStart)
  | .order => some (.rewind,relayState)
  | .rewind => none
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .width dispatch
def widthWord (x y : List Bool) := InputBlockDescriptors.widthWord x y
def blockWord (x y : List Bool) := InputBlockDescriptors.blockWord x y
def littlePrecision (x y : List Bool) := AffineTriple.triple 2 (blockWord x y).reverse
def precisionWord (x y : List Bool) := (littlePrecision x y).reverse
noncomputable def initialFrame (x y : List Bool) : machine.Cfg := machine.initCfg x y
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (x.map machine.bitSym++Sym.sep::y.map machine.bitSym)
    else if i=15 then machine.tapeOf ((widthWord x y).map machine.bitSym)
    else if i=16 then machine.tapeOf ((blockWord x y).map machine.bitSym)
    else if i=17 then machine.tapeOf ((precisionWord x y).map machine.bitSym)
    else if i=3 ∨ i=4 then WidthPreparation.descriptorTape (widthWord x y)
    else machine.tapeOf []
  head := fun i => if i=0 then x.length+y.length+2
    else if i=3 ∨ i=4 then (widthWord x y).length+1 else 0
end IntMul.InputArithmeticDescriptors


