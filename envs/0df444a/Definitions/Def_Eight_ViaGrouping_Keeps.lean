-- Prove2me | Definitions.Def_Eight_ViaGrouping_Keeps
-- name    : Eight_ViaGrouping_Keeps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:50:42.454432+00:00
-- url     : https://prove2.me/theorems/73d94313-cd8f-498f-953d-8e01e253f7e3
-- title:
--   Keeps
-- statement:
--   Definitions and structural lemmas for Keeps, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Keeps.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Theorems.Thm_Eight_SecNetworks_keeps_toPaperNetwork
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_decide_mem
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elem
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
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sprod
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_Prog_Count_linkB_polyT
import Theorems.Thm_Groundwork_Prog_Count_links_polyT
import Theorems.Thm_Groundwork_Prog_Count_litAt_polyT
import Theorems.Thm_Groundwork_Prog_Count_locals_polyT
import Theorems.Thm_Groundwork_Prog_Count_mu_polyT
import Theorems.Thm_Groundwork_Prog_Count_rows_polyT
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_polyT
import Theorems.Thm_Groundwork_Prog_Count_varAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_Pc_polyT
import Theorems.Thm_Groundwork_Prog_NetE_Uc_unary
import Theorems.Thm_Groundwork_Prog_NetE_betaC_polyT
import Theorems.Thm_Groundwork_Prog_NetE_capWord_polyT
import Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
import Theorems.Thm_Groundwork_Prog_NetE_col_polyT
import Theorems.Thm_Groundwork_Prog_NetE_isOne_polyT
import Theorems.Thm_Groundwork_Prog_NetE_isPsi_polyT
import Theorems.Thm_Groundwork_Prog_NetE_isW_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_members_polyT
import Theorems.Thm_Groundwork_Prog_NetE_nCol_polyT
import Theorems.Thm_Groundwork_Prog_NetE_nPairs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_nStates_polyT
import Theorems.Thm_Groundwork_Prog_NetE_n_polyT
import Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_qF_polyT
import Theorems.Thm_Groundwork_Prog_NetE_qW_polyT
import Theorems.Thm_Groundwork_Prog_NetE_stLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_validB_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Sparsify_polyT_addP
import Theorems.Thm_Groundwork_Sparsify_polyT_canonP
import Theorems.Thm_Groundwork_Sparsify_polyT_greedyP
import Theorems.Thm_Groundwork_Sparsify_polyT_litsOf
import Theorems.Thm_Groundwork_Sparsify_polyT_minusP
import Theorems.Thm_Groundwork_Sparsify_polyT_overP
import Theorems.Thm_Groundwork_Sparsify_polyT_pickP
import Theorems.Thm_Groundwork_Sparsify_polyT_redP
import Theorems.Thm_Groundwork_Sparsify_polyT_rootP
import Theorems.Thm_Groundwork_Sparsify_polyT_stepP
import Theorems.Thm_Groundwork_Sparsify_polyT_subP
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_digit_polyT
import Theorems.Thm_Groundwork_query0_polyT
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
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
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
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Prog.Count.linkB_polyT
attribute [local fun_prop] Groundwork.Prog.Count.links_polyT
attribute [local fun_prop] Groundwork.Prog.Count.litAt_polyT
attribute [local fun_prop] Groundwork.Prog.Count.locals_polyT
attribute [local fun_prop] Groundwork.Prog.Count.mu_polyT
attribute [local fun_prop] Groundwork.Prog.Count.rows_polyT
attribute [local fun_prop] Groundwork.Prog.Count.slotsOf_polyT
attribute [local fun_prop] Groundwork.Prog.Count.varAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.Pc_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.betaC_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.capWord_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.cap_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.col_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.labOf_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLen_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.members_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.n_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.prs_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.stLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zA_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zOf_polyT
attribute [local fun_prop] Groundwork.Sparsify.polyT_addP
attribute [local fun_prop] Groundwork.Sparsify.polyT_canonP
attribute [local fun_prop] Groundwork.Sparsify.polyT_greedyP
attribute [local fun_prop] Groundwork.Sparsify.polyT_litsOf
attribute [local fun_prop] Groundwork.Sparsify.polyT_minusP
attribute [local fun_prop] Groundwork.Sparsify.polyT_overP
attribute [local fun_prop] Groundwork.Sparsify.polyT_pickP
attribute [local fun_prop] Groundwork.Sparsify.polyT_redP
attribute [local fun_prop] Groundwork.Sparsify.polyT_rootP
attribute [local fun_prop] Groundwork.Sparsify.polyT_stepP
attribute [local fun_prop] Groundwork.Sparsify.polyT_subP
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


set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] [Enc C] [Carried C] (K g : ℕ) {Np : Procs C}
omit [HasSize C] [Carried C] in
/-- The test (G1) is computable in polynomial time. -/
theorem g1_polyT : PolyT fun cx : C × ℕ => (List.range K).all fun G => decide (K * (members K g cx.2 G).length ≤ 2 * g) := by
  have hl : PolyT fun q : (C × ℕ) × ℕ => K * (members K g q.1.2 q.2).length := by fun_prop
  exact PolyT.all (f := fun (cx : C × ℕ) G => decide (K * (members K g cx.2 G).length ≤ 2 * g)) (PolyT.decide_le hl (PolyT.const (2 * g))) (by fun_prop)
theorem g2_polyT (h : KeepsP Np) : PolyT fun cx : C × ℕ => (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1) := by
  have hk := keeps_toPaperNetwork h.keeps
  have hU : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => Uc g Np.toPaperNetwork q.1.1.1 := PolyT.comp (Uc_unary g hk).poly (by fun_prop)
  have hP : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => Np.P q.1.1.1 := PolyT.comp h.P.poly (by fun_prop)
  have hb : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => K * Uc g Np.toPaperNetwork q.1.1.1 + g * Np.P q.1.1.1 := ((PolyT.const K).mul hU).add ((PolyT.const g).mul hP)
  have hl : PolyT fun q : ((C × ℕ) × ℕ) × ℕ => K ^ 3 * lbLen K g Np.toPaperNetwork q.1.1.1 q.1.1.2 q.1.2 q.2 :=
    (PolyT.const (K ^ 3)).mul (lbLen_polyT K g hk (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  exact PolyT.all (f := fun (cx : C × ℕ) G => (List.range K).all fun G' =>
        G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1))
      (PolyT.all (f := fun (q : (C × ℕ) × ℕ) G' =>
          q.2 == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork q.1.1 q.1.2 q.2 G' ≤ K * Uc g Np.toPaperNetwork q.1.1 + g * Np.P q.1.1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb)) (by fun_prop)) (by fun_prop)
theorem goodP_polyT (h : KeepsP Np) : PolyT (goodP K g Np) := PolyT.and' (g1_polyT K g) (g2_polyT K g h)
omit [Carried C] in
/-- The query (b, z_b) is computable in polynomial time. -/
theorem qMb_polyT (h : Np.toPaperNetwork.Keeps) : PolyT (qMb K g Np) := by
  unfold qMb; fun_prop (disch := assumption)
omit [Carried C] in
/-- The query ((a, b), (z_a, z_b)) is computable in polynomial time. -/
theorem qPsi_polyT (h : Np.toPaperNetwork.Keeps) : PolyT (qPsi K g Np) := by
  unfold qPsi; fun_prop (disch := assumption)
@[instance_reducible] def wM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] : IsPolyT (wM K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.W) (qW_polyT K g h)
  gated_isPolyT _ _
@[instance_reducible] def psiP_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.Ψ] : IsPolyT (psiP K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.mem) (qMb_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.Ψ) (qPsi_polyT K g h)
  haveI := gated_isPolyT (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ)
  gated_isPolyT _ _
@[instance_reducible] def fM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.f] : IsPolyT (fM K g Np) :=
  haveI := IsPolyT.mapIn (M := Np.mem) (qW_polyT K g h)
  haveI := IsPolyT.mapIn (M := Np.f) (qF_polyT K g h)
  gated_isPolyT _ _
@[instance_reducible] def termP_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] [IsPolyT Np.Ψ] [IsPolyT Np.f] : IsPolyT (termP K g Np) :=
  haveI := wM_isPolyT K g h
  haveI := psiP_isPolyT K g h
  haveI := fM_isPolyT K g h
  haveI := IsPolyT.ite (M := psiP K g Np) (N := fM K g Np) (isPsi_polyT K g)
  haveI := IsPolyT.ite (M := wM K g Np) (N := Stepped.ite (isPsi K g) (psiP K g Np) (fM K g Np)) (isW_polyT g)
  haveI := IsPolyT.const (α := (X0 C × ℕ) × ℕ) (1 : ℤ)
  IsPolyT.ite (isOne_polyT K g)
@[instance_reducible] def tableM_isPolyT (h : Np.toPaperNetwork.Keeps) [IsPolyT Np.mem] [IsPolyT Np.W] [IsPolyT Np.Ψ] [IsPolyT Np.f] : IsPolyT (tableM K g Np) :=
  haveI := termP_isPolyT K g h
  haveI := IsPolyT.prodRange (M := termP K g Np) (N := nPairs g) (nPairs_polyT g)
  haveI := IsPolyT.sumRange (M := Stepped.prodRange (nPairs g) (termP K g Np)) (nStates_polyT K g h)
  haveI := IsPolyT.const (α := X0 C) (0 : ℤ)
  IsPolyT.ite (validB_polyT K g h)
@[instance_reducible] def searchP_isPolyT (h : KeepsP Np) : IsPolyT (searchP K g Np) :=
  haveI := IsPolyT.ofFun (goodP_polyT K g h)
  IsPolyT.firstRange (nCol_polyT K g) (by change PolyT fun b : Bool => b; fun_prop)
end Eight.ViaGrouping


