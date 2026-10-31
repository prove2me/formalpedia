-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
-- name    : MarkovProcess_V3H_Time_DenseTimeHistory_28830881
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:34.061927+00:00
-- url     : https://prove2.me/theorems/d3cffadb-f06f-4143-9e23-051bdf4cb824
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_DenseTimeHistory_28830881
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

namespace MarkovProcess

/-- A history through natural-number time `n`, including both endpoints. -/
abbrev DenseTimeHistory (α : Type*) (n : ℕ) := Set.Iic n → α

namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]

/-- The value-preserving equivalence from natural numbers at most `n` to `Fin (n + 1)`. -/
def iicEquivFin (n : ℕ) : Set.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i, Nat.lt_succ_iff.mpr i.property⟩
  invFun i := ⟨i, Nat.le_of_lt_succ i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem p2m_embedded_9eb8e8b3d137611a (n : ℕ) (i : Set.Iic n) : (iicEquivFin n i).val = i.val :=
  rfl

@[simp]
theorem p2m_embedded_eab6d0066ddd75b0 (n : ℕ) (i : Fin (n + 1)) :
    ((iicEquivFin n).symm i).val = i.val :=
  rfl

/-- Split a history into its time-zero value and its positive-time coordinates. -/
def historyEquiv (n : ℕ) : DenseTimeHistory α n ≃ᵐ α × (Fin n → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) ↦ α) (iicEquivFin n)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0)

@[simp]
theorem p2m_embedded_40297d6100e809cd (n : ℕ) (history : DenseTimeHistory α n) :
    (historyEquiv n history).1 = history ⟨0, Nat.zero_le n⟩ :=
  rfl

@[simp]
theorem p2m_embedded_06f77b24bbd3321f (n : ℕ) (history : DenseTimeHistory α n) (i : Fin n) :
    (historyEquiv n history).2 i = history ⟨i.succ, i.isLt⟩ :=
  rfl

@[simp]
theorem p2m_embedded_d937258dcf9d5cb6 (n : ℕ) (x : α) (path : Fin n → α) :
    (historyEquiv n).symm (x, path) ⟨0, Nat.zero_le n⟩ = x :=
  rfl

@[simp]
theorem p2m_embedded_4bc5af79b71d6d38 (n : ℕ) (x : α) (path : Fin n → α) (i : Fin n) :
    (historyEquiv n).symm (x, path) ⟨i.succ, i.isLt⟩ = path i :=
  rfl

/-- Split a finite path into its proper prefix and its last coordinate. -/
def splitLast (n : ℕ) : (Fin (n + 1) → α) ≃ᵐ (Fin n → α) × α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)).trans
    MeasurableEquiv.prodComm

@[simp]
theorem splitLast_fst_apply (n : ℕ) (path : Fin (n + 1) → α) (i : Fin n) :
    (splitLast n path).1 i = path i.castSucc := by
  change path ((Fin.last n).succAbove i) = path i.castSucc
  rw [Fin.succAbove_last_apply]

@[simp]
theorem splitLast_snd (n : ℕ) (path : Fin (n + 1) → α) :
    (splitLast n path).2 = path (Fin.last n) :=
  rfl

@[simp]
theorem splitLast_symm_apply_castSucc (n : ℕ) (path : Fin n → α) (x : α) (i : Fin n) :
    (splitLast n).symm (path, x) i.castSucc = path i := by
  have h := splitLast_fst_apply n ((splitLast n).symm (path, x)) i
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem splitLast_symm_apply_last (n : ℕ) (path : Fin n → α) (x : α) :
    (splitLast n).symm (path, x) (Fin.last n) = x := by
  have h := splitLast_snd n ((splitLast n).symm (path, x))
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

end DenseTimeHistory

end MarkovProcess


