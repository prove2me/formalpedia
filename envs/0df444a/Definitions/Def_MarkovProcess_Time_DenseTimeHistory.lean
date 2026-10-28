-- Prove2me | Definitions.Def_MarkovProcess_Time_DenseTimeHistory
-- name    : MarkovProcess_Time_DenseTimeHistory
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T11:55:48.332925+00:00
-- url     : https://prove2.me/theorems/080891d5-6980-4f29-ba40-4df6065700a1
-- title:
--   MarkovProcess definitions: Time.DenseTimeHistory
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Time.DenseTimeHistory`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/DenseTimeHistory.lean#L1-L97

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

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





/-- Split a history into its time-zero value and its positive-time coordinates. -/
def historyEquiv (n : ℕ) : DenseTimeHistory α n ≃ᵐ α × (Fin n → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) ↦ α) (iicEquivFin n)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0)









/-- Split a finite path into its proper prefix and its last coordinate. -/
def splitLast (n : ℕ) : (Fin (n + 1) → α) ≃ᵐ (Fin n → α) × α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)).trans
    MeasurableEquiv.prodComm









end DenseTimeHistory

end MarkovProcess


