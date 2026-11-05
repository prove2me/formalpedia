-- Prove2me | Definitions.Def_ToTuring_Poly_GridSide
-- name    : ToTuring_Poly_GridSide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:06:55.377136+00:00
-- url     : https://prove2.me/theorems/ccb33cc2-15d3-4e04-b077-6856d60b74a5
-- title:
--   Grid Side
-- statement:
--   Definitions and structural lemmas for Grid Side, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/GridSide.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Cut
import Definitions.Def_ToTuring_Poly_Grid
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_StepMachines_Prog_SidePresents
import Theorems.Thm_Groundwork_Grid_rectLen_le
import Theorems.Thm_Groundwork_Grid_sideCnt_rectDig_le
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_testBit
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
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_capW_polyT
import Theorems.Thm_Groundwork_digit_polyT
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_query0_polyT
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
import Theorems.Thm_Groundwork_sum_range_eq_list
import Theorems.Thm_Groundwork_tri_polyT
import Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.digit_polyT
attribute [local fun_prop] Groundwork.query0_polyT
attribute [local fun_prop] Groundwork.tri_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
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
namespace Groundwork.Prog
open Stepped
open Groundwork.Grid (sideCnt he node c2 rectIx rectDig rectLen sideChunk sideCap sideCnt_rectDig_le rectLen_le)
section plain
variable {α : Type} [Enc α] (g : ℕ) (tr : Bool)
@[fun_prop] theorem he_polyT {ℓ x u : α → ℕ} {z : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT z) (h3 : PolyT x)
    (h4 : PolyT u) : PolyT fun a => he g (ℓ a) (z a) (x a) (u a) := by unfold he; fun_prop
@[fun_prop] theorem node_polyT {a i : α → ℕ} (h1 : PolyT a) (h2 : PolyT i) : PolyT fun x => node g tr (a x) (i x) := by
  unfold node; fun_prop
@[fun_prop] theorem rectIx_polyT {p κ : α → ℕ} (h1 : PolyT p) (h2 : PolyT κ) :
    PolyT fun x => rectIx g tr (p x) (κ x) := by unfold rectIx; fun_prop
@[fun_prop] theorem rectDig_polyT {n y p κ : α → ℕ} (h1 : PolyT n) (h2 : PolyT y) (h3 : PolyT p) (h4 : PolyT κ) :
    PolyT fun x => rectDig g tr (n x) (y x) (p x) (κ x) := by unfold rectDig; fun_prop
theorem rectLen_polyT {n y p κ : α → ℕ} (hn : Unary n) (hy : PolyT y) (hp : PolyT p) (hκ : PolyT κ) :
    PolyT fun x => rectLen g tr (n x) (y x) (p x) (κ x) := by
  have := hn.poly
  unfold rectLen
  exact capW_polyT hn (by fun_prop) fun _ => sideCnt_rectDig_le _ _ _ _ _ _
theorem le_sum_range {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ f k) (m : ℕ) : m ≤ ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; have := hf m; omega
theorem drop_sum_eq {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ f k) (κ : ℕ) (w : List Bool) :
    w.drop (((List.range w.length).map fun κ' => if κ' < κ then f κ' else 0).sum) = w.drop (∑ κ' ∈ Finset.range κ, f κ') := by
  rw [← sum_range_eq_list]
  rcases le_or_gt κ w.length with h | h
  · congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [List.drop_eq_nil_of_le, List.drop_eq_nil_of_le]
    · exact h.le.trans (le_sum_range hf κ)
    · refine (le_sum_range hf w.length).trans (Finset.sum_le_sum fun k hk => ?_)
      rw [if_pos ((Finset.mem_range.1 hk).trans h)]
theorem one_le_rectLen (n y p κ : ℕ) : 1 ≤ rectLen g tr n y p κ := by
  unfold rectLen capW tb
  have : 0 < Nat.size (3 ^ sideCnt tr n (rectDig g tr n y p κ)) := Nat.size_pos.2 (by positivity)
  omega
theorem sideChunk_polyT {n y a b κ : α → ℕ} {θ : α → List Bool} (hn : Unary n) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hθ : PolyT θ) (hκ : PolyT κ) :
    PolyT fun x => sideChunk g tr (n x) (y x) (a x) (b x) (θ x) (κ x) := by
  have hn' := hn.poly
  have h1 : PolyT fun p : α × ℕ =>
      rectLen g tr (n p.1) (y p.1) (tri (min (a p.1) (b p.1)) (max (a p.1) (b p.1))) p.2 :=
    rectLen_polyT g tr (hn.comp (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun x => rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) (κ x) :=
    rectLen_polyT g tr hn hy (by fun_prop) hκ
  have h3 : PolyT fun x => List.range ((θ x).drop (g * n x)).length :=
    PolyT.range (Unary.of_length (w := fun x => (θ x).drop (g * n x)) (by fun_prop))
  have h : PolyT fun x =>
      (((θ x).drop (g * n x)).drop
        (((List.range ((θ x).drop (g * n x)).length).map fun κ' =>
          if κ' < κ x then rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ' else 0).sum)).take
        (rectLen g tr (n x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) (κ x)) := by fun_prop
  exact h.congr fun x => by rw [drop_sum_eq (one_le_rectLen g tr _ _ _), sideChunk, chunkAt]
@[fun_prop] theorem sideLabels_polyT {ℓ a i u : α → ℕ} {z : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT a) (h3 : PolyT z)
    (h4 : PolyT i) (h5 : PolyT u) : PolyT fun x => sideLabels g tr (ℓ x) (a x) (z x) (i x) (u x) := by
  unfold sideLabels; fun_prop
theorem viewAt_polyT {n y a b i i' : α → ℕ} {z θ : α → List Bool} (hn : Unary n) (hy : PolyT y) (ha : PolyT a)
    (hb : PolyT b) (hz : PolyT z) (hθ : PolyT θ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => viewAt g tr (n x) (y x) (a x) (b x) (z x) (θ x) (i x) (i' x) := by
  have hn' := hn.poly
  have := sideChunk_polyT g tr hn hy ha hb hθ (κ := fun x => tri (i x) (i' x)) (by fun_prop)
  unfold viewAt; fun_prop
end plain
section ctx
variable {C : Type} [Enc C] (g : ℕ) (tr : Bool) {lam : C → ℕ}
theorem sideChk_polyT (hl : PolyT lam) : PolyT (sideChk g tr lam) := by unfold sideChk; fun_prop
theorem sideQuery_polyT (hl : PolyT lam) : PolyT (sideQuery g tr lam) := by unfold sideQuery; fun_prop
theorem sideG_polyT : PolyT (sideG g : (C × ℕ) × WQ → ℕ) := by unfold sideG; fun_prop
theorem sideEdges_polyT (hl : PolyT lam) : PolyT (sideEdges g tr lam) := by unfold sideEdges; fun_prop
theorem sideIsRect_polyT : PolyT (sideIsRect g : ((C × ℕ) × FQ) × ℕ → Bool) := by unfold sideIsRect; fun_prop
theorem sideNN_polyT : PolyT (sideNN g : (C × ℕ) × FQ → ℕ) := by unfold sideNN; fun_prop
theorem sideView_polyT (hl : Unary lam) : PolyT (sideView g tr lam) := by
  unfold sideView
  exact viewAt_polyT g tr (hl.comp (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)
variable [HasSize C] [Carried C]
@[instance_reducible] def IsPolyT.sideWP {R : Stepped (C × IQ) ℤ} [IsPolyT R] (hl : PolyT lam) :
    IsPolyT (sideWP g tr lam R) :=
  haveI := IsPolyT.mapIn (M := R) (sideQuery_polyT g tr hl)
  haveI := IsPolyT.prodRange (M := mapIn (sideQuery g tr lam) R) (N := sideG g) (sideG_polyT g)
  haveI : IsPolyT (Stepped.const 0 : Stepped ((C × ℕ) × WQ) ℤ) := IsPolyT.const 0
  IsPolyT.ite (sideChk_polyT g tr hl)
@[instance_reducible] def IsPolyT.sideFP (hl : Unary lam) : IsPolyT (sideFP g tr lam) :=
  haveI := IsPolyT.cutP tr
  haveI := IsPolyT.mapIn (M := Prog.cutP tr) (sideView_polyT g tr hl)
  haveI : IsPolyT (Stepped.const 1 : Stepped (((C × ℕ) × FQ) × ℕ) ℤ) := IsPolyT.const 1
  haveI := IsPolyT.ite (M := mapIn (sideView g tr lam) (Prog.cutP tr)) (N := Stepped.const 1) (sideIsRect_polyT (C := C) g)
  haveI := IsPolyT.prodRange (M := Stepped.ite (sideIsRect g) (mapIn (sideView g tr lam) (Prog.cutP tr)) (Stepped.const 1))
    (N := sideNN g) (sideNN_polyT g)
  haveI : IsPolyT (Stepped.const 0 : Stepped ((C × ℕ) × FQ) ℤ) := IsPolyT.const 0
  IsPolyT.ite (sideEdges_polyT g tr hl.poly)
end ctx
end Groundwork.Prog


