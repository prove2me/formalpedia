-- Prove2me | Definitions.Def_IntMul_InputCarrySetup
-- name    : IntMul_InputCarrySetup
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T17:21:12.18339+00:00
-- url     : https://prove2.me/theorems/08b2748d-feab-4736-a740-2f767c0f0450
-- title:
--   Complete physical parameter and zero-carry setup from original multiplication input
-- statement:
--   A fixed eighteen-tape finite controller starts on the original input x#y with genuinely blank work tapes and all heads at cell zero. It computes canonical binary width, block-size, and precision descriptors; physically prepares precision countdown/template banks 13 and 14 from the retained precision word; writes the complete zero carry into bank 12; and rewinds all parameter and carry heads to their specified positions. The original input remains read-only and global output remains empty. Correctness, sufficient carry precision, exact final frame and a linear actual-transition clock are separate theorem obligations.
-- source:
--   Original complete physical input-to-parameter-and-carry preparation controller. Written by Codex.

import Definitions.Def_IntMul_InputArithmeticDescriptors
import Definitions.Def_IntMul_CarryInitialization
set_option maxHeartbeats 1000000
namespace IntMul.InputCarrySetup
open TapeCopy (Sym)
abbrev State := Option (InputArithmeticDescriptors.machine.K ⊕ CarryInitialization.machine.K)
def parameterState (q : InputArithmeticDescriptors.machine.K) : State :=
  match q with | none => none | some p => some (.inl (some p))
def carryState (q : CarryInitialization.machine.K) : State :=
  match q with | none => none | some p => some (.inr (some p))
def nativeTape (j : Fin 16) : Fin 18 :=
  if j.val=3 then 13 else if j.val=4 then 14 else if j.val=13 then 3 else if j.val=14 then 4
  else if j.val=15 then 17 else ⟨j.val,by omega⟩
def innerTape (i : Fin 18) (h : i.val≠15 ∧ i.val≠16) : Fin 16 :=
  if i.val=3 then 13 else if i.val=4 then 14 else if i.val=13 then 3 else if i.val=14 then 4
  else if h17 : i.val=17 then 15 else ⟨i.val,by have := i.isLt;rcases h with ⟨h15,h16⟩;omega⟩
def carryAction (a : Fin 18 → Sym) (r : Fin 16 → Sym × Move) (i : Fin 18) : Sym × Move :=
  if h : i.val≠15 ∧ i.val≠16 then r (innerTape i h) else (a i,.stay)
private theorem native_inner (i : Fin 18) (h : i.val≠15 ∧ i.val≠16) :
    nativeTape (innerTape i h)=i := by
  fin_cases i
  all_goals first | (exact False.elim (h.1 rfl)) | (exact False.elim (h.2 rfl)) | rfl
noncomputable def transition (q : State) (a : Fin 18 → Sym) : State × (Fin 18 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) => let r := InputArithmeticDescriptors.machine.δ q a;(parameterState r.1,r.2)
  | some (.inr q) => let r := CarryInitialization.machine.δ q (fun j => a (nativeTape j));
      (carryState r.1,carryAction a r.2)
private theorem transition_start (q : State) (a : Fin 18 → Sym) (i : Fin 18) (hi : a i=Sym.start) :
    ((transition q a).2 i).1=Sym.start ∧ ((transition q a).2 i).2≠Move.left := by
  cases q with
  | none =>
      change a i=Sym.start ∧ Move.stay≠Move.left
      exact ⟨hi,by decide⟩
  | some q =>
      cases q with
      | inl q => exact InputArithmeticDescriptors.machine.start_preserved q a i hi
      | inr q =>
          change (carryAction a (CarryInitialization.machine.δ q (fun j => a (nativeTape j))).2 i).1=Sym.start ∧
            (carryAction a (CarryInitialization.machine.δ q (fun j => a (nativeTape j))).2 i).2≠Move.left
          by_cases h : i.val≠15 ∧ i.val≠16
          · simp only [carryAction,dif_pos h]
            have hr : a (nativeTape (innerTape i h))=Sym.start := by rw [native_inner];exact hi
            exact CarryInitialization.machine.start_preserved q (fun j => a (nativeTape j)) (innerTape i h) hr
          · simp only [carryAction,dif_neg h]
            exact ⟨hi,by decide⟩

private theorem transition_no_new_start (q : State) (a : Fin 18 → Sym) (i : Fin 18) (hi : a i≠Sym.start) :
    ((transition q a).2 i).1≠Sym.start := by
  cases q with
  | none => exact hi
  | some q =>
      cases q with
      | inl q => exact InputArithmeticDescriptors.machine.start_only_at_start q a i hi
      | inr q =>
          change (carryAction a (CarryInitialization.machine.δ q (fun j => a (nativeTape j))).2 i).1≠Sym.start
          by_cases h : i.val≠15 ∧ i.val≠16
          · simp only [carryAction,dif_pos h]
            have hr : a (nativeTape (innerTape i h))≠Sym.start := by rw [native_inner];exact hi
            exact CarryInitialization.machine.start_only_at_start q (fun j => a (nativeTape j)) (innerTape i h) hr
          · simpa only [carryAction,dif_neg h] using hi

private theorem transition_input (q : State) (a : Fin 18 → Sym) : ((transition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some q =>
      cases q with
      | inl q => exact InputArithmeticDescriptors.machine.input_readonly q a
      | inr q => exact CarryInitialization.machine.input_readonly q (fun j => a (nativeTape j))

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  instFintypeK := by
    letI : Fintype InputArithmeticDescriptors.machine.K := InputArithmeticDescriptors.machine.instFintypeK
    letI : Fintype CarryInitialization.machine.K := CarryInitialization.machine.instFintypeK
    change Fintype (Option (InputArithmeticDescriptors.machine.K ⊕ CarryInitialization.machine.K))
    infer_instance
  qStart := parameterState InputArithmeticDescriptors.machine.qStart
  qHalt := none
  start_ne_halt := by exact Option.some_ne_none _
  k := 18
  two_le_k := by decide
  δ := transition
  start_preserved := transition_start
  start_only_at_start := transition_no_new_start
  halt_fixed := by intro a;rfl
  input_readonly := transition_input

noncomputable def dispatch (carry : Bool) (_a : Fin 18 → Sym) : Option (Bool × State) :=
  if carry then none else some (true,carryState CarryInitialization.machine.qStart)
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Bool false dispatch
noncomputable def parameterView (c : InputArithmeticDescriptors.machine.Cfg) : subroutine.Cfg where
  state := parameterState c.state
  cells := c.cells
  head := c.head
noncomputable def carryBase (x y : List Bool) : CarryInitialization.machine.Cfg where
  state := CarryInitialization.machine.qHalt
  cells := fun j => (InputArithmeticDescriptors.finalFrame x y).cells (nativeTape j)
  head := fun j => (InputArithmeticDescriptors.finalFrame x y).head (nativeTape j)
noncomputable def carryView (x y : List Bool) (c : CarryInitialization.machine.Cfg) : subroutine.Cfg where
  state := carryState c.state
  cells := fun i => if h : i.val≠15 ∧ i.val≠16 then c.cells (innerTape i h)
    else (InputArithmeticDescriptors.finalFrame x y).cells i
  head := fun i => if h : i.val≠15 ∧ i.val≠16 then c.head (innerTape i h)
    else (InputArithmeticDescriptors.finalFrame x y).head i
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := machine.qHalt
  cells := (carryView x y (CarryInitialization.finalFrame (carryBase x y)
    (InputArithmeticDescriptors.precisionWord x y))).cells
  head := (carryView x y (CarryInitialization.finalFrame (carryBase x y)
    (InputArithmeticDescriptors.precisionWord x y))).head
end IntMul.InputCarrySetup

#print axioms IntMul.InputCarrySetup.subroutine


