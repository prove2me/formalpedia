-- Prove2me | Definitions.Def_FD1D_Initialization
-- name    : FD1D_Initialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:04:23.796396+00:00
-- url     : https://prove2.me/theorems/22ecaf39-b3fa-5ae8-8376-8b29780103c0
-- title:
--   Initialization
-- statement:
--   Definitions and structural lemmas for Initialization, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators
abbrev Assignment (ι : Type*) (m : ℕ) := Fin m → ι
abbrev DyadicAssignment (L m : ℕ) := Assignment (DyadicNode L) m
def assignmentCount {ι : Type*} [DecidableEq ι] {m : ℕ}
    (ω : Assignment ι m) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => ω j = i).card
theorem sum_assignmentCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (ω : Assignment ι m) :
    ∑ i, assignmentCount ω i = m := by
  classical
  simp only [assignmentCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
def assignmentState {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (ω : Assignment ι m) : InventoryState ι m :=
  ⟨assignmentCount ω, sum_assignmentCount ω⟩
@[simp]
theorem assignmentState_count {ι : Type*} [Fintype ι]
    [DecidableEq ι] {m : ℕ} (ω : Assignment ι m) (i : ι) :
    (assignmentState ω).1 i = assignmentCount ω i :=
  rfl
def assignmentPerm {ι : Type*} {m : ℕ} (e : Equiv.Perm ι) :
    Equiv.Perm (Assignment ι m) :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) e
@[simp]
theorem assignmentPerm_apply {ι : Type*} {m : ℕ}
    (e : Equiv.Perm ι) (ω : Assignment ι m) (j : Fin m) :
    assignmentPerm e ω j = e (ω j) :=
  rfl
def inventoryStatePerm {ι : Type*} [Fintype ι] {m : ℕ}
    (e : Equiv.Perm ι) : Equiv.Perm (InventoryState ι m) where
  toFun x :=
    ⟨fun i => x.1 (e.symm i), by
      calc
        ∑ i, x.1 (e.symm i) = ∑ i, x.1 i :=
          Equiv.sum_comp e.symm x.1
        _ = m := x.2⟩
  invFun x :=
    ⟨fun i => x.1 (e i), by
      calc
        ∑ i, x.1 (e i) = ∑ i, x.1 i :=
          Equiv.sum_comp e x.1
        _ = m := x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp
def refreshedLaw (L m : ℕ) :
    FiniteLaw (InventoryState (DyadicNode L) m) :=
  (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m)).map assignmentState
end
end FD1D


