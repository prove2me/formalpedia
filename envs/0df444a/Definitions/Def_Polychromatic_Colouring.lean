-- Prove2me | Definitions.Def_Polychromatic_Colouring
-- name    : Polychromatic_Colouring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:34:34.468012+00:00
-- url     : https://prove2.me/theorems/6b3037d1-689c-433b-99d5-86d8179e99b3
-- title:
--   Colouring
-- statement:
--   Definitions and structural lemmas for Colouring, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Pointwise
section
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
lemma IsPolychrom.nonempty (h : IsPolychrom S χ) :
    S.Nonempty := by
  obtain ⟨i, hi, hi'⟩ := h 0 (χ 0)
  use i
section decEq
variable [DecidableEq G]
lemma isPolychrom_iff :
    IsPolychrom S χ ↔ ∀ n : G, ∀ k : K, ∃ i ∈ n +ᵥ S, χ i = k := by
  simp [IsPolychrom, Finset.mem_vadd_finset]
set_option linter.unusedSimpArgs false in
lemma isPolychrom_iff_surjOn :
    IsPolychrom S χ ↔ ∀ n : G, Set.SurjOn χ (n +ᵥ S) Set.univ := by
  simp [isPolychrom_iff, Set.SurjOn, Set.subset_def, ← Finset.coe_vadd_finset]
alias ⟨IsPolychrom.surjOn, _⟩ := isPolychrom_iff_surjOn
lemma isPolychrom_iff_mem_image [DecidableEq K] :
    IsPolychrom S χ ↔ ∀ n : G, ∀ k, k ∈ (n +ᵥ S).image χ := by simp [isPolychrom_iff]
alias ⟨IsPolychrom.mem_image, _⟩ := isPolychrom_iff_mem_image
end decEq
@[reducible] def IsPolychrom.fintype [DecidableEq K] (hχ : IsPolychrom S χ) :
    Fintype K where
  elems := S.image χ
  complete := by classical simpa using hχ.mem_image 0
lemma IsPolychrom.vadd [DecidableEq G] (n : G) (h : IsPolychrom S χ) : IsPolychrom (n +ᵥ S) χ := by
  rw [isPolychrom_iff] at h ⊢
  simp_rw [vadd_vadd]
  intro n
  exact h _
@[simp] lemma isPolychrom_vadd [DecidableEq G] {n : G} : IsPolychrom (n +ᵥ S) χ ↔ IsPolychrom S χ :=
  ⟨fun h ↦ by simpa using h.vadd (-n), fun h ↦ h.vadd n⟩
instance [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K] : Decidable (IsPolychrom S χ) :=
  inferInstanceAs (Decidable (∀ _, _))
def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ
lemma HasPolychromColouring.nonempty_set (h : HasPolychromColouring K S) : S.Nonempty := by
  obtain ⟨χ, hχ⟩ := h
  exact hχ.nonempty
@[simp] lemma not_hasPolychromColouring_empty : ¬ HasPolychromColouring K (∅ : Finset G) := by
  intro h
  simpa using h.nonempty_set
@[simp] lemma hasPolychromColouring_vadd [DecidableEq G] {n : G} :
    HasPolychromColouring K (n +ᵥ S) ↔ HasPolychromColouring K S := by simp [HasPolychromColouring]
alias ⟨_, HasPolychromColouring.vadd⟩ := hasPolychromColouring_vadd
end


