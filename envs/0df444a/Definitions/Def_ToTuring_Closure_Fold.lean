-- Prove2me | Definitions.Def_ToTuring_Closure_Fold
-- name    : ToTuring_Closure_Fold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:21:25.717923+00:00
-- url     : https://prove2.me/theorems/8777dd30-1fad-4638-99a2-66ef46534600
-- title:
--   Fold
-- statement:
--   Definitions and structural lemmas for Fold, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Fold.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_exit
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_iter
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_consF_within
import Theorems.Thm_Groundwork_TM_fromA_within
import Theorems.Thm_Groundwork_TM_fromB_within
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_pop1_within
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_toA_within
import Theorems.Thm_Groundwork_TM_toB_within
import Theorems.Thm_Groundwork_TM_unconsF_within
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_le_len
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
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
def foldHead : TM2.Stmt (fun _ : Stk => Sym) Unit (Option Sym) :=
  .pop .main (fun _ _ => none) <| .pop .main (fun _ o => o) <|
    .branch (fun s => s == some .R) (.load (fun _ => none) .halt)
      (.push .main (fun s => s.getD .L) <| .load (fun _ => none) <| .goto fun _ => ())
def foldBody (P : Fr) : Fr :=
  ((((((mv .main .a).seq (mv .main .b)).seq pop1).seq (mv .a .main)).seq consF).seq P).seq (mv .b .main)
def foldLoop (P : Fr) : Fr := Frag.loop foldHead (foldBody P)
theorem code_ne_R (x : V) : ∃ s w, code x = s :: w ∧ (s == Sym.R) = false := by
  cases x with
  | nil => exact ⟨_, _, rfl, by decide⟩
  | bit b => exact ⟨_, _, rfl, by simp⟩
  | cons x y => exact ⟨_, _, rfl, by decide⟩
theorem foldHead_nil (M A B N : List Sym) :
    TM2.stepAux foldHead none (st (.L :: .R :: M) A B N) = ⟨none, none, st M A B N⟩ := by
  simp [foldHead, TM2.stepAux]
theorem foldHead_cons (x : V) (M A B N : List Sym) :
    TM2.stepAux foldHead none (st (.L :: (code x ++ M)) A B N) = ⟨some (), none, st (code x ++ M) A B N⟩ := by
  obtain ⟨s, w, e, hs⟩ := code_ne_R x
  simp [foldHead, TM2.stepAux, e, hs]
def roundT (t : ℕ → ℕ) (Lb Bd : ℕ) : ℕ := 6 * Lb + 2 * Bd + 12 + t (Lb + Bd + 2)
theorem foldLoop_within {σ : Type} [Enc σ] {h : ε × σ → σ} {P : Fr} {t : ℕ → ℕ} (ht : Monotone t)
    (hP : ∀ (p : ε × σ) (M A B N : List Sym), P.Within (st (wd p ++ M) A B N) (t (len p)) (st (wd (h p) ++ M) A B N))
    (Lb Bd : ℕ) (M A B N : List Sym) : ∀ (l : List ε) (s : σ), len l ≤ Lb →
      (∀ k, len ((l.take k).foldl (fun s e => h (e, s)) s) ≤ Bd) →
      (foldLoop P).Within (st (wd l ++ (wd s ++ M)) A B N) (l.length * roundT t Lb Bd + 1)
        (st (wd (l.foldl (fun s e => h (e, s)) s) ++ M) A B N)
  | [], s, _, _ => by
    refine ⟨1, by simp, ?_⟩
    exact Frag.loop_runs_exit (foldHead_nil _ A B N)
  | e :: r, s, hL, hB => by
    have hs : len s ≤ Bd := by simpa using hB 0
    have hlc := len_cons e r
    have ih := foldLoop_within ht hP Lb Bd M A B N r (h (e, s)) (by omega) (fun k => by simpa using hB (k + 1))
    -- the body
    have b1 := toA_within (Enc.toV e) (wd r ++ (.R :: (wd s ++ M))) A B N
    have b2 := toB_within (Enc.toV r) (.R :: (wd s ++ M)) (mirror (wd e) ++ A) B N
    have b3 := pop1_within (wd s ++ M) (mirror (wd e) ++ A) (mirror (wd r) ++ B) N .R
    have b4 := fromA_within (Enc.toV e) (wd s ++ M) A (mirror (wd r) ++ B) N
    have b5 := consF_within (Enc.toV e) (Enc.toV s) M A (mirror (wd r) ++ B) N
    have b6 := hP (e, s) M A (mirror (wd r) ++ B) N
    have b7 := fromB_within (Enc.toV r) (wd (h (e, s)) ++ M) A B N
    obtain ⟨n, hn, hbody⟩ := (((((b1.seq b2).seq b3).seq b4).seq b5).seq b6).seq b7
    obtain ⟨m, hm, hrest⟩ := ih
    have hhead := foldHead_cons (Enc.toV e) (wd r ++ (.R :: (wd s ++ M))) A B N
    have e0 : wd (e :: r) ++ (wd s ++ M) = .L :: (code (Enc.toV e) ++ (wd r ++ (.R :: (wd s ++ M)))) := by
      simp only [wd_cons, List.cons_append, List.append_assoc]
      rfl
    refine ⟨1 + n + m, ?_, ?_⟩
    · have h1 : t (len (e, s)) ≤ t (Lb + Bd + 2) := ht (by rw [len_pair]; omega)
      have h2 : (code (Enc.toV e)).length = len e := rfl
      have h3 : (code (Enc.toV r)).length = len r := rfl
      have h4 : (code (Enc.toV s)).length = len s := rfl
      rw [h2, h3, h4] at hn
      have h5 : (e :: r).length * roundT t Lb Bd = r.length * roundT t Lb Bd + roundT t Lb Bd := by
        rw [List.length_cons, Nat.succ_mul]
      unfold roundT at h5 ⊢
      unfold roundT at hm
      omega
    · rw [e0]
      exact Frag.loop_runs_iter hhead hbody hrest
omit [Enc α] [Enc γ] [Enc ε] in
/-- The fold keeps the context in the first component of its state. -/
theorem foldl_ctx (g : α → γ → ε → γ) (x : α) : ∀ (l : List ε) (c : γ),
    l.foldl (fun (s : α × γ) e => (s.1, g s.1 s.2 e)) (x, c) = (x, l.foldl (g x) c)
  | [], _ => rfl
  | e :: r, c => by simp only [List.foldl_cons]; exact foldl_ctx g x r _
theorem foldl {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2)
    (hB : ∃ t, PB t ∧ ∀ x (k : ℕ), len (((l x).take k).foldl (g x) (a x)) ≤ t (len x)) :
    PolyT (fun x => (l x).foldl (g x) (a x)) := by
  obtain ⟨tB, htB, hB⟩ := hB
  -- the step on states (x, c), the start, the end
  have hh : PolyT fun p : ε × α × γ => (p.2.1, g p.2.1 p.2.2 p.1) :=
    prodMk (by fun_prop) (comp (g := fun p : ε × α × γ => (p.2.1, p.2.2, p.1)) hg (by fun_prop))
  have h0 : PolyT fun x => (l x, (x, a x)) := by fun_prop
  have h1 : PolyT fun s : α × γ => s.2 := by fun_prop
  obtain ⟨P, t, htp, htm, hP, -⟩ := hh.elim
  obtain ⟨Q, q, hqp, hqm, hQ, hQl⟩ := h0.elim
  obtain ⟨Z, z, hzp, hzm, hZ, -⟩ := h1.elim
  refine PolyT.of (((Q.seq unconsF).seq (foldLoop P)).seq Z)
    (t := fun n => q n + (2 * q n + 6) + (q n * roundT t (q n) (n + tB n + 2) + 1) + z (n + tB n + 2)) (s := tB)
    ?_ htB (fun x M A B N => ?_) (fun x => by simpa using hB x (l x).length)
  · unfold roundT
    have hb : PB fun n => n + tB n + 2 := (PB.id'.add htB).add (PB.const 2)
    exact (((hqp.add (((PB.const 2).mul hqp).add (PB.const 6))).add ((hqp.mul (((((PB.const 6).mul hqp).add
      ((PB.const 2).mul hb)).add (PB.const 12)).add (htp.comp ((hqp.add hb).add (PB.const 2))))).add (PB.const 1)))).add
      (hzp.comp hb)
  · have hlen := hQl x
    rw [len_pair, len_pair] at hlen
    have c1 := hQ x M A B N
    have c2 := unconsF_within (Enc.toV (l x)) (Enc.toV (x, a x)) M A B N
    have hst : ∀ k, len (((l x).take k).foldl (fun (s : α × γ) e => (s.1, g s.1 s.2 e)) (x, a x)) ≤ len x + tB (len x) + 2 := by
      intro k
      rw [foldl_ctx, len_pair]
      have := hB x k
      omega
    have c3 := foldLoop_within (h := fun p : ε × α × γ => (p.2.1, g p.2.1 p.2.2 p.1)) htm hP (q (len x))
      (len x + tB (len x) + 2) M A B N (l x) (x, a x) (by omega) hst
    rw [foldl_ctx] at c3
    have c4 := hZ (x, (l x).foldl (g x) (a x)) M A B N
    refine (((c1.seq c2).seq c3).seq c4).mono ?_
    have e1 : (code (Enc.toV (l x))).length = len (l x) := rfl
    have e2 : (code (Enc.toV (x, a x))).length = len (x, a x) := rfl
    have e3 : z (len (x, (l x).foldl (g x) (a x))) ≤ z (len x + tB (len x) + 2) := hzm (by
      rw [len_pair]; have := hB x (l x).length; simp only [List.take_length] at this; omega)
    have e4 : (l x).length * roundT t (q (len x)) (len x + tB (len x) + 2) ≤
        q (len x) * roundT t (q (len x)) (len x + tB (len x) + 2) :=
      Nat.mul_le_mul_right _ ((length_le_len _).trans (by omega))
    rw [e1, e2, len_pair]
    omega
end Groundwork.PolyT


