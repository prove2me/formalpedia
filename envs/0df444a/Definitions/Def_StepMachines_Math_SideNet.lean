-- Prove2me | Definitions.Def_StepMachines_Math_SideNet
-- name    : StepMachines_Math_SideNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:06:26.782825+00:00
-- url     : https://prove2.me/theorems/ea176ec1-e784-4c89-9682-ec614fe6a46e
-- title:
--   Side Net
-- statement:
--   Definitions and structural lemmas for Side Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_Groundwork_Grid_tri_bijOn
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
namespace Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
def rectDig (g : ℕ) (tr : Bool) (n y p κ : ℕ) : ℕ := digit n y (rectIx g tr p κ)
def rectLen (g : ℕ) (tr : Bool) (n y p κ : ℕ) : ℕ := capW n (sideCnt tr n (rectDig g tr n y p κ))
def sideCuts (g : ℕ) (tr : Bool) (n y : ℕ) : Rect (Fin g) (Fin g) → Cut (Bits n) (Fin n → Bell) :=
  fun ω => sideCut tr n (rectDig g tr n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))
def bell0 (n : ℕ) : Fin n → Bell := fun _ => (false, false)
def sideNet (g : ℕ) (tr : Bool) (n : ℕ) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) :
    Network (Fin g) (RowSt (Fin g) (Fin g) (Bits n)) (RowLab (Fin g) (Bits n) (Fin n → Bell)) :=
  rowNet R (sideCuts g tr n y) (bell0 n) n
def rectC (g : ℕ) (tr : Bool) (n y p κ : ℕ) :
    Code (sparseLab (sideS0 tr) n (sideCnt tr n (rectDig g tr n y p κ))) (rectLen g tr n y p κ) :=
  Code.sparse (sideS0 tr) n (sideCnt tr n (rectDig g tr n y p κ))
def rectsC (g : ℕ) (tr : Bool) (n y : ℕ) (a b : Fin g) :
    Code (tuples (fun k : Fin g × Fin g => k.1 < k.2) (fun k => (sideCuts g tr n y ((a, b), k)).lab) (bell0 n))
      (∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ) :=
  Code.seq _ (fun k : Fin g × Fin g => tri k.1 k.2) (c2 g) (tri_bijOn g) (rectLen g tr n y (tri a b))
    (fun k => (rectC g tr n y (tri a b) (tri k.1 k.2)).D) (fun k => (rectC g tr n y (tri a b) (tri k.1 k.2)).dec)
    (fun k _ w hw => (rectC g tr n y (tri a b) (tri k.1 k.2)).len w hw)
    (fun k _ => (rectC g tr n y (tri a b) (tri k.1 k.2)).bij) (bell0 n)
theorem sum_pairs_tri (g : ℕ) (f : ℕ → ℕ) :
    ∑ k : Fin g × Fin g with k.1 < k.2, f (tri k.1 k.2) = ∑ κ ∈ range (c2 g), f κ := by
  have hb := tri_bijOn g
  refine Finset.sum_nbij (fun k : Fin g × Fin g => tri k.1 k.2) (fun k hk => ?_) (fun k hk k' hk' h => ?_)
    (fun κ hκ => ?_) (fun k _ => rfl)
  · exact hb.mapsTo (by simpa using hk)
  · exact hb.injOn (by simpa using hk) (by simpa using hk') h
  · obtain ⟨k, hk, rfl⟩ := hb.surjOn hκ
    exact ⟨k, by simpa using hk, rfl⟩
theorem sideNet_c_eq {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ = (sideNet g tr n R y).c a b := by
  simp only [sideNet, rowNet, Fintype.card_fin, min_eq_left hab.le, max_eq_right hab.le]
  rw [← sum_pairs_tri]
  rfl
theorem sideNet_Θ {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (univ : Finset (Fin g → Bits n)) ×ˢ
      tuples (fun k : Fin g × Fin g => k.1 < k.2) (fun k => (sideCuts g tr n y ((a, b), k)).lab) (bell0 n)
      = (sideNet g tr n R y).Θ a b := by
  simp [sideNet, rowNet, rowΘ, hab]
theorem sideNet_Θ_empty {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : ¬ a < b) :
    ∅ = (sideNet g tr n R y).Θ a b := by
  simp [sideNet, rowNet, hab]
def sideCl (g : ℕ) (tr : Bool) (n : ℕ) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) (a b : Fin g) :
    Code ((sideNet g tr n R y).Θ a b) ((sideNet g tr n R y).c a b) :=
  if hab : a < b then ((vC g n).prod (rectsC g tr n y a b)).cast (sideNet_Θ tr R y hab) (sideNet_c_eq tr R y hab)
  else (Code.empty ((fun _ _ => false), fun _ => bell0 n) _).cast (sideNet_Θ_empty tr R y hab) rfl
noncomputable def sideN (g : ℕ) (tr : Bool) : SideNet g := fun n Rm y =>
  (sideNet g tr n (sideR g tr n Rm) y).pull (fun _ => g ^ 3 * n) (fun _ => stC g tr n) (sideCl g tr n (sideR g tr n Rm) y)
noncomputable def sideZ (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) : ℤ :=
  ZG (sideR g false n Rm) fun ω => A n (patOf g n y ω)
def sideCap (g : ℕ) (tr : Bool) (n y a b : ℕ) : ℕ :=
  g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri (min a b) (max a b)) κ
end Groundwork.Grid


