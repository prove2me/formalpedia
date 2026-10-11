-- Prove2me | Definitions.Def_IntMul_InputParameterBanks
-- name    : IntMul_InputParameterBanks
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T17:40:38.744985+00:00
-- url     : https://prove2.me/theorems/55159ef4-3c28-4039-9cd6-461e572a00f6
-- title:
--   Complete physical arithmetic parameter-bank setup from original multiplication input
-- statement:
--   A fixed eighteen-tape finite controller starts from the exact x#y initial configuration with blank work tapes and all heads at zero. It computes width, block-size and sufficient carry-precision descriptors; prepares the width and precision countdown/template banks; generates a complete zero carry on bank 12; and physically copies the block descriptor from retained bank 16 to arithmetic bank 6. All descriptor/carry heads finish at their stated markers or countdown endpoints. Original input cells are retained and global output remains empty. Full configuration correctness and an actual linear transition clock are separate obligations.
-- source:
--   Original complete physical input-derived arithmetic parameter-bank setup. Written by Codex.

import Definitions.Def_IntMul_InputCarrySetup
import Definitions.Def_IntMul_DescriptorCopy
namespace IntMul.InputParameterBanks
open TapeCopy (Sym)
abbrev State := Option (InputCarrySetup.machine.K ⊕ DescriptorCopy.State)
def parameterState (q : InputCarrySetup.machine.K) : State :=
  match q with | none => none | some p => some (.inl (some p))
def copyState (q : DescriptorCopy.State) : State := if q=.halt then none else some (.inr q)
def copyTape (j : Fin 3) : Fin 18 := if j.val=0 then 0 else if j.val=1 then 16 else 6
def copyAction (a : Fin 18 → Sym) (r : Fin 3 → Sym × Move) (i : Fin 18) : Sym × Move :=
  if i.val=0 then r 0 else if i.val=16 then r 1 else if i.val=6 then r 2 else (a i,.stay)
noncomputable def transition (q : State) (a : Fin 18 → Sym) : State × (Fin 18 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) => let r := InputCarrySetup.machine.δ q a;(parameterState r.1,r.2)
  | some (.inr q) => let r := DescriptorCopy.machine.δ q (fun j => a (copyTape j));(copyState r.1,copyAction a r.2)
private theorem transition_start (q : State) (a : Fin 18 → Sym) (i : Fin 18) (hi : a i=Sym.start) :
    ((transition q a).2 i).1=Sym.start ∧ ((transition q a).2 i).2≠Move.left := by
  cases q with
  | none =>
      change a i=Sym.start ∧ Move.stay≠Move.left
      exact ⟨hi,by decide⟩
  | some q =>
      cases q with
      | inl q => exact InputCarrySetup.machine.start_preserved q a i hi
      | inr q =>
          fin_cases i
          · exact DescriptorCopy.machine.start_preserved q (fun j => a (copyTape j)) 0 hi
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact DescriptorCopy.machine.start_preserved q (fun j => a (copyTape j)) 2 hi
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
          · exact DescriptorCopy.machine.start_preserved q (fun j => a (copyTape j)) 1 hi
          · exact ⟨hi,by change Move.stay≠Move.left;decide⟩
private theorem transition_no_start (q : State) (a : Fin 18 → Sym) (i : Fin 18) (hi : a i≠Sym.start) :
    ((transition q a).2 i).1≠Sym.start := by
  cases q with
  | none => exact hi
  | some q =>
      cases q with
      | inl q => exact InputCarrySetup.machine.start_only_at_start q a i hi
      | inr q =>
          fin_cases i
          · exact DescriptorCopy.machine.start_only_at_start q (fun j => a (copyTape j)) 0 hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact DescriptorCopy.machine.start_only_at_start q (fun j => a (copyTape j)) 2 hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact hi
          · exact DescriptorCopy.machine.start_only_at_start q (fun j => a (copyTape j)) 1 hi
          · exact hi
private theorem transition_input (q : State) (a : Fin 18 → Sym) : ((transition q a).2 0).1=a 0 := by
  cases q with
  | none => rfl
  | some q =>
      cases q with
      | inl q => exact InputCarrySetup.machine.input_readonly q a
      | inr q => exact DescriptorCopy.machine.input_readonly q (fun j => a (copyTape j))
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
    letI : Fintype InputCarrySetup.machine.K := InputCarrySetup.machine.instFintypeK
    change Fintype (Option (InputCarrySetup.machine.K ⊕ DescriptorCopy.State))
    infer_instance
  qStart := parameterState InputCarrySetup.machine.qStart
  qHalt := none
  start_ne_halt := by exact Option.some_ne_none _
  k := 18
  two_le_k := by decide
  δ := transition
  start_preserved := transition_start
  start_only_at_start := transition_no_start
  halt_fixed := by intro a;rfl
  input_readonly := transition_input
noncomputable def dispatch (copy : Bool) (_a : Fin 18 → Sym) : Option (Bool × State) :=
  if copy then none else some (true,copyState .advance)
noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Bool false dispatch
noncomputable def parameterView (c : InputCarrySetup.machine.Cfg) : subroutine.Cfg where
  state := parameterState c.state
  cells := c.cells
  head := c.head
noncomputable def copyBase (x y : List Bool) : DescriptorCopy.machine.Cfg where
  state := .halt
  cells := fun j => (InputCarrySetup.finalFrame x y).cells (copyTape j)
  head := fun j => (InputCarrySetup.finalFrame x y).head (copyTape j)
noncomputable def copyView (x y : List Bool) (c : DescriptorCopy.machine.Cfg) : subroutine.Cfg where
  state := copyState c.state
  cells := fun i => if i.val=0 then c.cells 0 else if i.val=16 then c.cells 1 else if i.val=6 then c.cells 2
    else (InputCarrySetup.finalFrame x y).cells i
  head := fun i => if i.val=0 then c.head 0 else if i.val=16 then c.head 1 else if i.val=6 then c.head 2
    else (InputCarrySetup.finalFrame x y).head i
noncomputable def finalFrame (x y : List Bool) : machine.Cfg where
  state := machine.qHalt
  cells := (copyView x y (DescriptorCopy.finalFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y))).cells
  head := (copyView x y (DescriptorCopy.finalFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y))).head
end IntMul.InputParameterBanks
#print axioms IntMul.InputParameterBanks.subroutine


