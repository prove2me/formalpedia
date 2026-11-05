-- Prove2me | Definitions.Def_PaddedDescent_F_MarkLayers
-- name    : PaddedDescent_F_MarkLayers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:32:42.205202+00:00
-- url     : https://prove2.me/theorems/2d2458b8-982d-4b49-bb8d-90e12a6dda0b
-- title:
--   Mark Layers
-- statement:
--   Definitions and structural lemmas for Mark Layers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
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
namespace PaddedDescent.F.Mark
open Finset Groundwork.Prog
namespace Layers
theorem nvio_cons (σ : ℕ → Bool) (C : Cl) (L : Fml) : nvio σ (C :: L) = nvio σ L + if vio σ C = true then 1 else 0 := by
  simp [nvio, List.countP_cons]
theorem drop_step (X B κ d w : ℕ) (h : X * 2 ^ (κ + d + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + d + 1))
    (hB : B * 2 ^ (κ + d + 3) ≤ 3 ^ κ * 2 ^ w) :
    (X + B) * 2 ^ (κ + (d + 1) + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + (d + 1) + 1) := by
  have e1 : 2 ^ (κ + (d + 1) + 2) = 2 * 2 ^ (κ + d + 2) := by ring
  have e2 : 2 ^ (w + κ + (d + 1) + 1) = 2 * 2 ^ (w + κ + d + 1) := by ring
  have e3 : 2 ^ (κ + d + 3) = 2 * 2 ^ (κ + d + 2) := by ring
  rw [e1, e2]; rw [e3] at hB
  nlinarith
theorem keep_step (Y B κ d w : ℕ) (h : (Y + B) * 2 ^ (κ + d + 2) + 3 ^ κ * 2 ^ w ≤ 2 ^ (w + κ + d + 1))
    (hB : 3 ^ κ * 2 ^ w < B * 2 ^ (κ + d + 3)) :
    Y * 2 ^ (κ + 1 + d + 2) + 3 ^ (κ + 1) * 2 ^ w ≤ 2 ^ (w + (κ + 1) + d + 1) := by
  have e1 : 2 ^ (κ + 1 + d + 2) = 2 * 2 ^ (κ + d + 2) := by ring
  have e2 : 2 ^ (w + (κ + 1) + d + 1) = 2 * 2 ^ (w + κ + d + 1) := by ring
  have e3 : 2 ^ (κ + d + 3) = 2 * 2 ^ (κ + d + 2) := by ring
  have e4 : 3 ^ (κ + 1) = 3 * 3 ^ κ := by ring
  rw [e1, e2, e4]; rw [e3] at hB
  nlinarith
end Layers
open Layers
def satL (σ : ℕ → Bool) (Ls : List Fml) : Prop := ∀ L ∈ Ls, nvio σ L = 0
instance decSatL (σ : ℕ → Bool) (Ls : List Fml) : Decidable (satL σ Ls) := by unfold satL; infer_instance
def XX (n : ℕ) (Λ : Fml) (rest : List Fml) : ℕ :=
  ∑ σ : Fin n → Bool, if satL (ext σ) rest then 2 ^ nvio (ext σ) Λ else 0
def BB (n : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : ℕ :=
  ∑ σ : Fin n → Bool, if satL (ext σ) rest ∧ vio (ext σ) C = true then 2 ^ nvio (ext σ) Λ else 0
def InvS (n w : ℕ) (Λ : Fml) (rest : List Fml) : Prop :=
  XX n Λ rest * 2 ^ (rest.flatten.length + Λ.length + 2) + 3 ^ rest.flatten.length * 2 ^ w ≤ 2 ^ (w + rest.flatten.length + Λ.length + 1)
def Inv (n w : ℕ) : List Fml → Prop
  | [] => True
  | [_] => True
  | Λ :: L :: rest => InvS n w Λ (L :: rest) ∧ Inv n w (L :: rest)
def dropC (n w : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : Prop :=
  BB n C Λ rest * 2 ^ (rest.flatten.length + Λ.length + 3) ≤ 3 ^ rest.flatten.length * 2 ^ w
instance decDropC (n w : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : Decidable (dropC n w C Λ rest) := by unfold dropC; infer_instance
def placeM (n w : ℕ) (C : Cl) : List Fml → List Fml
  | [] => []
  | [Λ] => [C :: Λ]
  | Λ :: L :: rest => if dropC n w C Λ (L :: rest) then (C :: Λ) :: L :: rest else Λ :: placeM n w C (L :: rest)
theorem placeM_ne_nil {n w : ℕ} {C : Cl} : ∀ {Ls : List Fml}, Ls ≠ [] → placeM n w C Ls ≠ []
  | [_], _ => by simp [placeM]
  | Λ :: L :: rest, _ => by
    rw [placeM]; split_ifs <;> simp
theorem satL_cons {σ : ℕ → Bool} {L : Fml} {Ls : List Fml} : satL σ (L :: Ls) ↔ nvio σ L = 0 ∧ satL σ Ls := by
  simp [satL]
theorem satL_placeM {n w : ℕ} {C : Cl} (σ : ℕ → Bool) : ∀ {Ls : List Fml}, Ls ≠ [] →
    (satL σ (placeM n w C Ls) ↔ satL σ Ls ∧ vio σ C = false)
  | [Λ], _ => by
    simp only [placeM, satL_cons, nvio_cons]
    cases vio σ C <;> simp [satL]
  | Λ :: L :: rest, _ => by
    rw [placeM]
    split_ifs
    · simp only [satL_cons, nvio_cons]
      cases vio σ C <;> simp
    · rw [satL_cons, satL_placeM σ (by simp), satL_cons (L := Λ)]
      tauto
theorem length_flatten_placeM {n w : ℕ} {C : Cl} : ∀ {Ls : List Fml}, Ls ≠ [] →
    (placeM n w C Ls).flatten.length = Ls.flatten.length + 1
  | [Λ], _ => by simp [placeM]
  | Λ :: L :: rest, _ => by
    rw [placeM]
    split_ifs
    · simp only [List.flatten_cons, List.length_append, List.length_cons]; omega
    · rw [List.flatten_cons, List.length_append, length_flatten_placeM (by simp), List.flatten_cons (l := Λ), List.length_append]
      omega
theorem XX_cons (n : ℕ) (C : Cl) (Λ : Fml) (rest : List Fml) : XX n (C :: Λ) rest = XX n Λ rest + BB n C Λ rest := by
  unfold XX BB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [nvio_cons]
  by_cases h : satL (ext σ) rest <;> cases hv : vio (ext σ) C <;> simp [h, pow_succ, mul_two]
theorem XX_keep (n : ℕ) (C : Cl) (Λ : Fml) {rest rest' : List Fml}
    (h : ∀ σ : Fin n → Bool, satL (ext σ) rest' ↔ satL (ext σ) rest ∧ vio (ext σ) C = false) :
    XX n Λ rest' + BB n C Λ rest = XX n Λ rest := by
  unfold XX BB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : satL (ext σ) rest <;> cases hv : vio (ext σ) C <;> simp [h σ, h1, hv]
theorem Inv.placeM {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Inv n w Ls → Inv n w (placeM n w C Ls)
  | [], _ => trivial
  | [_], _ => trivial
  | Λ :: L :: rest, h => by
    rw [Mark.placeM]
    split_ifs with hd
    · refine ⟨?_, h.2⟩
      have := drop_step _ _ _ _ _ h.1 hd
      unfold InvS
      rw [XX_cons, List.length_cons]
      exact this
    · obtain ⟨L', rest', e⟩ : ∃ L' rest', Mark.placeM n w C (L :: rest) = L' :: rest' :=
        List.exists_cons_of_ne_nil (placeM_ne_nil (by simp))
      have ih := Inv.placeM C h.2
      have hl := length_flatten_placeM (n := n) (w := w) (C := C) (Ls := L :: rest) (by simp)
      have hx := XX_keep n C Λ (rest := L :: rest) (rest' := Mark.placeM n w C (L :: rest)) fun σ => satL_placeM _ (by simp)
      rw [e] at ih hl hx ⊢
      refine ⟨?_, ih⟩
      unfold InvS
      rw [hl]
      have h1 := h.1
      unfold InvS at h1
      rw [← hx] at h1
      exact keep_step _ _ _ _ _ h1 (not_le.1 hd)
theorem Inv.drop {n w : ℕ} : ∀ {Ls : List Fml} (i : ℕ), Inv n w Ls → Inv n w (Ls.drop i)
  | _, 0, h => h
  | [], _ + 1, _ => trivial
  | [_], _ + 1, _ => by simp [Inv]
  | _ :: L :: rest, i + 1, h => by
    rw [List.drop_succ_cons]
    exact Inv.drop i h.2
def layersM (n w R : ℕ) (ψ : Fml) : List Fml := ψ.foldl (fun Ls C => placeM n w C Ls) (List.replicate (R + 1) [])
end PaddedDescent.F.Mark
namespace PaddedDescent.F
end PaddedDescent.F


