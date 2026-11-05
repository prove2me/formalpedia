-- Prove2me | Definitions.Def_ClauseBound_Alg_GridNet
-- name    : ClauseBound_Alg_GridNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:27:36.888252+00:00
-- url     : https://prove2.me/theorems/8e69624b-bc43-4a16-acf0-40d358bc94a6
-- title:
--   Grid Net
-- statement:
--   Definitions and structural lemmas for Grid Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_tri_bijOn
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Run_trans
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
namespace ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
def gridE (p d : ℕ) : (tr : Bool) → Fin (p * d) ≃ Fin (nParts p d tr) × Fin (nMemb p d tr)
  | false => finProdFinEquiv.symm
  | true => finProdFinEquiv.symm.trans (Equiv.prodComm _ _)
def nodeC (p d : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin (nParts p d tr) × Fin (nMemb p d tr) → Bits n)) (p * d * n) :=
  ((bitsC n).blocks (gridE p d tr).symm).cast Fintype.piFinset_univ rfl
def stC (p d : ℕ) (tr : Bool) (n : ℕ) :
    Code (univ : Finset (RowSt (Fin (nParts p d tr)) (Fin (nMemb p d tr)) (Bits n))) (nMemb p d tr * (p * d) * n) :=
  ((nodeC p d tr n).blocks (Equiv.refl (Fin (nMemb p d tr)))).cast Fintype.piFinset_univ (Nat.mul_assoc _ _ _).symm
noncomputable def gridR (p d : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) (gridE p d tr)
section Net
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
def cutG (i : ℕ) : Cut (Bits ℓ) (List Bool) where
  lab := words (P.cap tr h ℓ i)
  top x y θ := P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))
  bot u v θ := P.bot ((pad, tr), (h, i), (bitsOf u, bitsOf v, θ))
  cap := P.cap tr h ℓ i
def cutsG : Rect (Fin (nParts p d tr)) (Fin (nMemb p d tr)) → Cut (Bits ℓ) (List Bool) :=
  fun ω => cutG P pad tr h ℓ (digG P d tr h ℓ y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))
def gridNet (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) :
    Network (Fin (nParts p d tr)) (RowSt (Fin (nParts p d tr)) (Fin (nMemb p d tr)) (Bits ℓ)) (RowLab (Fin (nMemb p d tr)) (Bits ℓ) (List Bool)) :=
  rowNet R (cutsG P pad p d tr h ℓ y) [] ℓ
def rectsC (a b : Fin (nParts p d tr)) :
    Code (tuples (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => k.1 < k.2) (fun k => (cutsG P pad p d tr h ℓ y ((a, b), k)).lab) [])
      (∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :=
  Code.seq _ (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => tri k.1 k.2) (c2 (nMemb p d tr)) (tri_bijOn (nMemb p d tr))
    (lenG P d tr h ℓ y (tri a b)) (fun k => words (lenG P d tr h ℓ y (tri a b) (tri k.1 k.2))) (fun _ => id)
    (fun _ _ _ hw => mem_words.1 hw) (fun _ _ => Set.bijOn_id _) []
variable {P pad p d tr h ℓ y}
theorem gridNet_c_eq (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ = (gridNet P pad p d tr h ℓ y R).c a b := by
  simp only [gridNet, rowNet, Fintype.card_fin, min_eq_left hab.le, max_eq_right hab.le]
  rw [← sum_pairs_tri]
  rfl
theorem gridNet_Θ (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (univ : Finset (Fin (nMemb p d tr) → Bits ℓ)) ×ˢ
      tuples (fun k : Fin (nMemb p d tr) × Fin (nMemb p d tr) => k.1 < k.2) (fun k => (cutsG P pad p d tr h ℓ y ((a, b), k)).lab) []
      = (gridNet P pad p d tr h ℓ y R).Θ a b := by
  simp [gridNet, rowNet, rowΘ, hab]
theorem gridNet_Θ_empty (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : ¬ a < b) :
    ∅ = (gridNet P pad p d tr h ℓ y R).Θ a b := by
  simp [gridNet, rowNet, hab]
variable (P pad p d tr h ℓ y)
def gridCl (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) (a b : Fin (nParts p d tr)) :
    Code ((gridNet P pad p d tr h ℓ y R).Θ a b) ((gridNet P pad p d tr h ℓ y R).c a b) :=
  if hab : a < b then ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).cast (gridNet_Θ R hab) (gridNet_c_eq R hab)
  else (Code.empty ((fun _ _ => false), fun _ => []) _).cast (gridNet_Θ_empty R hab) rfl
noncomputable def gridN (Rm : Inst (Fin (p * d)) (List Bool)) : Network (Fin (nParts p d tr)) (List Bool) (List Bool) :=
  (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).pull (fun _ => nMemb p d tr * (p * d) * ℓ) (fun _ => stC p d tr ℓ)
    (gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm))
end Net
def ixG (p d : ℕ) (ω : Rect (Fin p) (Fin d)) : ℕ := tri ω.1.1 ω.1.2 * c2 d + tri ω.2.1 ω.2.2
def patG (p d n y : ℕ) : Rect (Fin p) (Fin d) → ℕ :=
  fun ω => if ω ∈ Ω (Fin p) (Fin d) then digit n y (ixG p d ω) else 0
noncomputable def gridR0 (p d n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) : Inst (Fin p × Fin d) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) finProdFinEquiv.symm
noncomputable def termZ (p d ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n y : ℕ) : ℤ :=
  ZG (gridR0 p d ℓ Rm) fun ω => A (patG p d n y ω)
def trA {ℓ : ℕ} : Bool → Pieces.Four ℓ → Pieces.Four ℓ
  | false, F => F
  | true, F => fun x y u v => F x u y v
structure CutsOK (P : PiecesF) (pad : U) (h ℓ : ℕ) (A : ℕ → Pieces.Four ℓ) : Prop where
  cnt_pos : 1 ≤ P.cnt h ℓ
  m_pos : 1 ≤ P.m
  factors : ∀ tr, ∀ i < P.cnt h ℓ, (cutG P pad tr h ℓ i).Factors (trA tr (A i))
  cap_le : ∀ tr, ∀ i < P.cnt h ℓ, P.cap tr h ℓ i ≤ 2 * P.m * ℓ
  abs_A : ∀ i < P.cnt h ℓ, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h ℓ
  abs_top : ∀ tr, ∀ i < P.cnt h ℓ, ∀ x y θ, |(cutG P pad tr h ℓ i).top x y θ| ≤ 2 ^ P.bits h ℓ
  abs_bot : ∀ tr, ∀ i < P.cnt h ℓ, ∀ x y θ, |(cutG P pad tr h ℓ i).bot x y θ| ≤ 2 ^ P.bits h ℓ
section Facts
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
end Facts
end ClauseBound.Alg.GridNet


