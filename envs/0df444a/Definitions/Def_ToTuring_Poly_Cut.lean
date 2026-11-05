-- Prove2me | Definitions.Def_ToTuring_Poly_Cut
-- name    : ToTuring_Poly_Cut
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:01:54.854796+00:00
-- url     : https://prove2.me/theorems/1ce37ce4-4045-48f3-9612-999dceb28154
-- title:
--   Cut
-- statement:
--   Definitions and structural lemmas for Cut, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Cut.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_StepMachines_Prog_CutProg
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
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
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_length
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
import Theorems.Thm_P2M_Groundwork_PolyT_table__55b65ec90c5c
import Theorems.Thm_P2M_Groundwork_PolyT_toWord__1c2f60d1d666
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
namespace Groundwork.Prog
open Stepped
open Groundwork.Grid (sideCnt topTerm botTerm)
variable {α : Type} [Enc α]
@[fun_prop] theorem top_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.top (h x) (p x) (q x) :=
  PolyT.table₃ c.top hh hp hq
@[fun_prop] theorem bot0_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.bot0 (h x) (p x) (q x) :=
  PolyT.table₃ c.bot0 hh hp hq
@[fun_prop] theorem bot1_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.bot1 (h x) (p x) (q x) :=
  PolyT.table₃ c.bot1 hh hp hq
@[fun_prop] theorem oth_polyT {s₀ : α → Bell} {d : α → ℕ} (hs : PolyT s₀) (hd : PolyT d) :
    PolyT fun x => oth (s₀ x) (d x) := by
  unfold oth; fun_prop
@[fun_prop] theorem symAt_polyT {s₀ : α → Bell} {n k : α → ℕ} {w : α → List Bool} (hs : PolyT s₀) (hn : PolyT n)
    (hw : PolyT w) (hk : PolyT k) : PolyT fun x => symAt (s₀ x) (n x) (w x) (k x) := by
  unfold symAt; fun_prop
@[fun_prop] theorem validW_polyT {n c : α → ℕ} {w : α → List Bool} (hn : PolyT n) (hc : PolyT c) (hw : PolyT w) :
    PolyT fun x => validW (n x) (c x) (w x) := by
  unfold validW; fun_prop
@[fun_prop] theorem sideCnt_polyT (tr : Bool) {n i : α → ℕ} (hn : PolyT n) (hi : PolyT i) :
    PolyT fun x => sideCnt tr (n x) (i x) := by
  unfold sideCnt; fun_prop
@[fun_prop] theorem toWordL_polyT {w : α → List Bool} {y : α → ℕ} (hw : PolyT w) (hy : PolyT y) :
    PolyT fun x => toWord (w x).length (y x) :=
  PolyT.toWord' (Unary.of_length hw) hy
@[fun_prop] theorem topTerm_polyT (tr : Bool) {x y w : α → List Bool} {k : α → ℕ} (hx : PolyT x) (hy : PolyT y)
    (hw : PolyT w) (hk : PolyT k) : PolyT fun a => topTerm tr (x a) (y a) (w a) (k a) := by
  unfold topTerm; fun_prop
@[fun_prop] theorem botTerm_polyT (tr : Bool) {x y w : α → List Bool} {s k : α → ℕ} (hx : PolyT x) (hy : PolyT y)
    (hw : PolyT w) (hs : PolyT s) (hk : PolyT k) : PolyT fun a => botTerm tr (x a) (y a) (w a) (s a) (k a) := by
  unfold botTerm; fun_prop
theorem cutLen_polyT : PolyT cutLen := by unfold cutLen; fun_prop
theorem cutValid_polyT (tr : Bool) : PolyT (cutValid tr) := by unfold cutValid; fun_prop
theorem cutTop_polyT : PolyT cutTop := by unfold cutTop; fun_prop
theorem topE_polyT (tr : Bool) : PolyT (topE tr) := by unfold topE; fun_prop
theorem cutPow_polyT : PolyT cutPow := PolyT.two_pow (e := fun q : CutQ => q.2.1.length) (Unary.of_length (by fun_prop))
theorem cutPop_polyT : PolyT cutPop := by unfold cutPop; fun_prop
theorem cutLen'_polyT : PolyT cutLen' := by unfold cutLen'; fun_prop
theorem botE_polyT (tr : Bool) : PolyT (botE tr) := by unfold botE; fun_prop
@[instance_reducible] def IsPolyT.cutP (tr : Bool) : IsPolyT (cutP tr) :=
  haveI := IsPolyT.ofFun (topE_polyT tr)
  haveI := IsPolyT.prodRange (M := ofFun (topE tr)) cutLen_polyT
  haveI := IsPolyT.ofFun (botE_polyT tr)
  haveI := IsPolyT.prodRange (M := ofFun (botE tr)) cutLen'_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped (CutQ × ℕ) ℤ) := IsPolyT.const 0
  haveI := IsPolyT.ite (M := prodRange cutLen' (ofFun (botE tr))) (N := Stepped.const 0) cutPop_polyT
  haveI := IsPolyT.sumRange (M := Stepped.ite cutPop (prodRange cutLen' (ofFun (botE tr))) (Stepped.const 0)) cutPow_polyT
  haveI := IsPolyT.ite (M := prodRange cutLen (ofFun (topE tr)))
    (N := sumRange cutPow (Stepped.ite cutPop (prodRange cutLen' (ofFun (botE tr))) (Stepped.const 0))) cutTop_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped CutQ ℤ) := IsPolyT.const 0
  IsPolyT.ite (cutValid_polyT tr)
end Groundwork.Prog


