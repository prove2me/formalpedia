-- Prove2me | Definitions.Def_ToTuring_Lib_List1b
-- name    : ToTuring_Lib_List1b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T18:30:37.625785+00:00
-- url     : https://prove2.me/theorems/2b3bcd17-bc56-4d28-b1c7-e08a6deb9f74
-- title:
--   List1b
-- statement:
--   Definitions and structural lemmas for List1b, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1b.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List1
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_listCases
import Theorems.Thm_Groundwork_PolyT_map
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
import Theorems.Thm_Groundwork_len_le_of_mem
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
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
@[fun_prop] theorem flatten {l : α → List (List β)} (hl : PolyT l) :
    PolyT (fun x => (l x).flatten) :=
  (flatMap (f := fun _ b => b) (by fun_prop) hl).congr fun x => by simp
@[fun_prop] theorem isEmpty {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).isEmpty) :=
  (listCases (d := fun _ => true) (f := fun _ _ _ => false) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl
@[fun_prop] theorem head? {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).head?) :=
  (listCases (d := fun _ => none) (f := fun _ e _ => some e) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl
@[fun_prop] theorem headD {l : α → List β} {d : α → β} (hl : PolyT l) (hd : PolyT d) :
    PolyT (fun x => (l x).headD (d x)) :=
  (listCases (d := d) (f := fun _ e _ => e) hl hd (by fun_prop)).congr
    fun x => by cases l x <;> rfl
@[fun_prop] theorem tail {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).tail) :=
  (listCases (d := fun _ => []) (f := fun _ _ r => r) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl
@[fun_prop] theorem getLast? {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).getLast?) :=
  (head? (reverse hl)).congr fun x => by simp
def zipStep (s : List γ × List (β × γ)) (e : β) : List γ × List (β × γ) :=
  match s.1 with
  | [] => s
  | c :: r => (r, (e, c) :: s.2)
theorem zipStep_poly : PolyT fun p : (List γ × List (β × γ)) × β => zipStep p.1 p.2 :=
  (listCases (l := fun p : (List γ × List (β × γ)) × β => p.1.1) (d := fun p => p.1)
    (f := fun p c r => (r, (p.2, c) :: p.1.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr
    fun p => by rcases p with ⟨⟨_ | ⟨c, r⟩, acc⟩, e⟩ <;> rfl
omit [Enc β] [Enc γ] in
/-- What the fold of the step computes. -/
theorem foldl_zipStep (l : List β) (r : List γ) (acc : List (β × γ)) :
    l.foldl zipStep (r, acc) = (r.drop l.length, (l.zip r).reverse ++ acc) := by
  induction l generalizing r acc with
  | nil => simp
  | cons e l ih =>
    cases r with
    | nil => simpa [zipStep] using ih [] acc
    | cons c r => simpa [zipStep] using ih r ((e, c) :: acc)
@[fun_prop] theorem zip {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).zip (l' x)) := by
  obtain ⟨_, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT fun x => (l x).foldl zipStep (l' x, ([] : List (β × γ))) :=
    foldl_add (g := fun _ => zipStep) hl (by fun_prop)
      (comp (g := fun p : α × (List γ × List (β × γ)) × β => (p.2.1, p.2.2)) zipStep_poly (by fun_prop))
      ⟨fun n => t n + 2, ht.add (PB.const 2), by
        rintro x ⟨_ | ⟨c, r⟩, acc⟩ e he
        · exact Nat.le_add_right _ _
        · have h1 := len_le_of_mem he
          have h2 := hlen x
          change len (r, (e, c) :: acc) ≤ len (c :: r, acc) + (t (len x) + 2)
          rw [len_pair, len_pair, len_cons, len_cons, len_pair]
          omega⟩
  exact (reverse (snd h)).congr fun x => by simp [foldl_zipStep]
@[fun_prop] theorem optionMap {f : α → β → γ} {o : α → Option β} (hf : PolyT fun p : α × β => f p.1 p.2) (ho : PolyT o) :
    PolyT (fun x => (o x).map (f x)) :=
  (optionElim (d := fun _ => none) (f := fun x b => some (f x b)) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl
@[fun_prop] theorem optionBind {f : α → β → Option γ} {o : α → Option β} (hf : PolyT fun p : α × β => f p.1 p.2) (ho : PolyT o) :
    PolyT (fun x => (o x).bind (f x)) :=
  (optionElim (d := fun _ => none) (f := f) ho (by fun_prop) hf).congr
    fun x => by cases o x <;> rfl
@[fun_prop] theorem optionGetD {o : α → Option β} {d : α → β} (ho : PolyT o) (hd : PolyT d) :
    PolyT (fun x => (o x).getD (d x)) :=
  (optionElim (d := d) (f := fun _ b => b) ho hd (by fun_prop)).congr
    fun x => by cases o x <;> rfl
@[fun_prop] theorem optionIsSome {o : α → Option β} (ho : PolyT o) :
    PolyT (fun x => (o x).isSome) :=
  (optionElim (d := fun _ => false) (f := fun _ _ => true) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl
@[fun_prop] theorem optionIsNone {o : α → Option β} (ho : PolyT o) :
    PolyT (fun x => (o x).isNone) :=
  (optionElim (d := fun _ => true) (f := fun _ _ => false) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl
def eqStep [DecidableEq β] (s : Bool × List β) (e : β) : Bool × List β :=
  match s.2 with
  | [] => (false, [])
  | c :: r => (s.1 && decide (e = c), r)
theorem eqStep_poly [DecidableEq β] [EqT β] : PolyT fun p : (Bool × List β) × β => eqStep p.1 p.2 :=
  (listCases (l := fun p : (Bool × List β) × β => p.1.2) (d := fun _ => (false, []))
    (f := fun p c r => (p.1.1 && decide (p.2 = c), r)) (by fun_prop) (by fun_prop) (by fun_prop)).congr
    fun p => by rcases p with ⟨⟨b, _ | ⟨c, r⟩⟩, e⟩ <;> rfl
omit [Enc β] in
/-- What the fold of the step computes. -/
theorem foldl_eqStep [DecidableEq β] (l r : List β) (b : Bool) :
    ((l.foldl eqStep (b, r)).1 && (l.foldl eqStep (b, r)).2.isEmpty) = (b && decide (l = r)) := by
  induction l generalizing r b with
  | nil => cases r <;> simp
  | cons e l ih =>
    cases r with
    | nil => simpa [eqStep] using ih [] false
    | cons c r => simpa [eqStep, Bool.and_assoc] using ih r (b && decide (e = c))
instance [DecidableEq β] [EqT β] : EqT (List β) := ⟨by
  have hb : ∀ b : Bool, len b = 1 := fun _ => rfl
  have h : PolyT fun p : List β × List β => p.1.foldl eqStep (true, p.2) :=
    foldl_add (g := fun _ => eqStep) (by fun_prop) (by fun_prop)
      (comp (g := fun p : (List β × List β) × (Bool × List β) × β => (p.2.1, p.2.2)) eqStep_poly (by fun_prop))
      ⟨fun _ => 0, PB.const 0, by
        rintro x ⟨b, _ | ⟨c, r⟩⟩ e -
        · change len (false, ([] : List β)) ≤ len (b, ([] : List β)) + 0
          rw [len_pair, len_pair, hb, hb]
        · change len (b && decide (e = c), r) ≤ len (b, c :: r) + 0
          rw [len_pair, len_pair, len_cons, hb, hb]
          omega⟩
  exact (and' (fst h) (isEmpty (snd h))).congr fun p => by simpa using foldl_eqStep p.1 p.2 true⟩
end Groundwork.PolyT


