-- Prove2me | Definitions.Def_ToTuring_EncLemmas
-- name    : ToTuring_EncLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:46.543207+00:00
-- url     : https://prove2.me/theorems/7827d8a4-d315-4d98-ae17-87edc56bfe43
-- title:
--   Enc Lemmas
-- statement:
--   Definitions and structural lemmas for Enc Lemmas, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit


set_option autoImplicit false
section
section
namespace Groundwork
open TM Enc
variable {α β : Type} [Enc α] [Enc β]
theorem wd_pair (a : α) (b : β) : wd (a, b) = .L :: (wd a ++ wd b ++ [.R]) := rfl
theorem wd_cons (a : α) (l : List α) : wd (a :: l) = .L :: (wd a ++ wd l ++ [.R]) := rfl
theorem wd_some (a : α) : wd (some a) = .L :: (wd a ++ [.L, .R] ++ [.R]) := rfl
theorem wd_inl (a : α) : wd (Sum.inl a : α ⊕ β) = .L :: ([.bit false] ++ wd a ++ [.R]) := rfl
theorem wd_inr (b : β) : wd (Sum.inr b : α ⊕ β) = .L :: ([.bit true] ++ wd b ++ [.R]) := rfl
theorem len_pair (a : α) (b : β) : len (a, b) = len a + len b + 2 := by
  simp only [len, wd_pair, List.length_cons, List.length_append, List.length_nil]
theorem len_nil : len ([] : List α) = 2 := rfl
theorem len_cons (a : α) (l : List α) : len (a :: l) = len a + len l + 2 := by
  simp only [len, wd_cons, List.length_cons, List.length_append, List.length_nil]
theorem len_none : len (none : Option α) = 2 := rfl
theorem len_some (a : α) : len (some a) = len a + 4 := by
  simp only [len, wd_some, List.length_cons, List.length_append, List.length_nil]
theorem len_inl (a : α) : len (Sum.inl a : α ⊕ β) = len a + 3 := by
  simp only [len, wd_inl, List.length_cons, List.length_append, List.length_nil]; omega
theorem len_inr (b : β) : len (Sum.inr b : α ⊕ β) = len b + 3 := by
  simp only [len, wd_inr, List.length_cons, List.length_append, List.length_nil]; omega
theorem len_bool (b : Bool) : len b = 1 := rfl
theorem len_unit (u : Unit) : len u = 2 := rfl
theorem len_bools (w : List Bool) : len w = 3 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [len_cons, ih, List.length_cons, len_bool]; omega
theorem len_nat (n : ℕ) : len n = 3 * Nat.size n + 2 := by
  rw [← Nat.size_eq_bits_len, ← len_bools]; rfl
theorem len_int (z : ℤ) : len z = 3 * Nat.size z.natAbs + 5 := by
  have h : len z = len (decide (z < 0), z.natAbs) := rfl
  rw [h, len_pair, len_bool, len_nat]; omega
instance : Carried Unit := ⟨fun u => by rw [len_unit, size_unit]; omega⟩
instance : Carried Bool := ⟨fun b => by rw [len_bool, size_bool]; omega⟩
instance : Carried ℕ := ⟨fun n => by rw [len_nat, size_nat]; omega⟩
instance : Carried ℤ := ⟨fun z => by rw [len_int, size_int]; omega⟩
instance [HasSize α] [HasSize β] [Carried α] [Carried β] : Carried (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    have h₁ := Carried.le a
    have h₂ := Carried.le b
    rw [len_pair, size_prod]; dsimp only; omega⟩
instance [HasSize α] [HasSize β] [Carried α] [Carried β] : Carried (α ⊕ β) :=
  ⟨fun s => by
    rcases s with a | b
    · have := Carried.le a; rw [len_inl, size_inl]; omega
    · have := Carried.le b; rw [len_inr, size_inr]; omega⟩
instance [HasSize α] [Carried α] : Carried (Option α) :=
  ⟨fun o => by
    rcases o with _ | a
    · rw [len_none, size_none]; omega
    · have := Carried.le a; rw [len_some, size_some]; omega⟩
instance [HasSize α] [Carried α] : Carried (List α) :=
  ⟨fun l => by
    induction l with
    | nil => rw [len_nil]; simp
    | cons a l ih =>
      have := Carried.le a
      rw [size_list] at ih
      rw [len_cons, size_list, List.map_cons, List.sum_cons]; omega⟩
end Groundwork


