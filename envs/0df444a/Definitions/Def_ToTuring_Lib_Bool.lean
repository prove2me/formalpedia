-- Prove2me | Definitions.Def_ToTuring_Lib_Bool
-- name    : ToTuring_Lib_Bool
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:23:01.655667+00:00
-- url     : https://prove2.me/theorems/15f79957-d8ce-4f99-8b8b-47faee8489b6
-- title:
--   Bool
-- statement:
--   Definitions and structural lemmas for Bool, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Bool.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sumElim
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
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
namespace Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
@[fun_prop] theorem and' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x && g x) := by
  exact (cond' hf hg (const false)).congr fun x => by cases f x <;> rfl
@[fun_prop] theorem or' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x || g x) := by
  exact (cond' hf (const true) hg).congr fun x => by cases f x <;> rfl
@[fun_prop] theorem not' {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => !f x) := by
  exact (cond' hf (const false) (const true)).congr fun x => by cases f x <;> rfl
@[fun_prop] theorem xor' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x ^^ g x) := by
  exact (cond' hf (not' hg) hg).congr fun x => by cases f x <;> cases g x <;> rfl
@[fun_prop] theorem toNat' {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => (f x).toNat) := by
  exact (cond' hf (const 1) (const 0)).congr fun x => by cases f x <;> rfl
@[fun_prop] theorem decide_eq_true {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => decide (f x = true)) := by
  exact hf.congr fun x => by cases f x <;> rfl
@[fun_prop] theorem decide_eq_false {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => decide (f x = false)) := by
  exact (not' hf).congr fun x => by cases f x <;> rfl
@[fun_prop] theorem decide_and {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PolyT fun x => decide (p x))
    (hq : PolyT fun x => decide (q x)) :
    PolyT (fun x => decide (p x ∧ q x)) := by
  exact (and' hp hq).congr fun x => (Bool.decide_and _ _).symm
@[fun_prop] theorem decide_or {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PolyT fun x => decide (p x))
    (hq : PolyT fun x => decide (q x)) :
    PolyT (fun x => decide (p x ∨ q x)) := by
  exact (or' hp hq).congr fun x => (Bool.decide_or _ _).symm
@[fun_prop] theorem decide_not {p : α → Prop} [DecidablePred p] (hp : PolyT fun x => decide (p x)) :
    PolyT (fun x => decide (¬ p x)) := by
  exact (not' hp).congr fun x => (_root_.decide_not (p := p x)).symm
class EqT (β : Type) [Enc β] [DecidableEq β] : Prop where
  eq : PolyT fun p : β × β => decide (p.1 = p.2)
@[fun_prop] theorem decide_eq [DecidableEq β] [EqT β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x = g x)) := by
  exact comp EqT.eq (prodMk hf hg)
@[fun_prop] theorem decide_ne [DecidableEq β] [EqT β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x ≠ g x)) := by
  exact decide_not (decide_eq hf hg)
@[fun_prop] theorem beq' [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x == g x) := by
  exact (decide_eq hf hg).congr fun x => (beq_eq_decide _ _).symm
@[fun_prop] theorem bne' [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x != g x) := by
  exact (not' (beq' hf hg)).congr fun _ => rfl
instance : EqT Bool :=
  ⟨(not' (xor' (fst id') (snd id'))).congr fun p => by rcases p with ⟨_ | _, _ | _⟩ <;> rfl⟩
instance : EqT Unit := ⟨(const true).congr fun _ => rfl⟩
instance [DecidableEq β] [DecidableEq γ] [EqT β] [EqT γ] : EqT (β × γ) :=
  ⟨(and' (decide_eq (fst (fst id')) (fst (snd id'))) (decide_eq (snd (fst id')) (snd (snd id')))).congr fun p => by
    rw [← Bool.decide_and]; exact decide_eq_decide.2 Prod.ext_iff.symm⟩
instance [DecidableEq β] [EqT β] : EqT (Option β) :=
  ⟨(optionElim (o := fun p : Option β × Option β => p.1) (d := fun p => p.2.elim true fun _ => false)
      (f := fun p a => p.2.elim false fun b => decide (a = b)) (fst id')
      (optionElim (f := fun _ _ => false) (snd id') (const true) (const false))
      (optionElim (o := fun q : (Option β × Option β) × β => q.1.2) (f := fun q b => decide (q.2 = b)) (snd (fst id'))
        (const false) (decide_eq (snd (fst id')) (snd id')))).congr fun p => by
    rcases p with ⟨_ | a, _ | b⟩ <;> simp⟩
instance [DecidableEq β] [DecidableEq γ] [EqT β] [EqT γ] : EqT (β ⊕ γ) :=
  ⟨(sumElim (s := fun p : (β ⊕ γ) × (β ⊕ γ) => p.1)
      (f := fun p a => p.2.elim (fun b => decide (a = b)) fun _ => false)
      (g := fun p a => p.2.elim (fun _ => false) fun b => decide (a = b)) (fst id')
      (sumElim (s := fun q : ((β ⊕ γ) × (β ⊕ γ)) × β => q.1.2) (f := fun q b => decide (q.2 = b)) (g := fun _ _ => false)
        (snd (fst id')) (decide_eq (snd (fst id')) (snd id')) (const false))
      (sumElim (s := fun q : ((β ⊕ γ) × (β ⊕ γ)) × γ => q.1.2) (f := fun _ _ => false) (g := fun q b => decide (q.2 = b))
        (snd (fst id')) (const false) (decide_eq (snd (fst id')) (snd id')))).congr fun p => by
    rcases p with ⟨a | a, b | b⟩ <;> simp⟩
end Groundwork.PolyT


