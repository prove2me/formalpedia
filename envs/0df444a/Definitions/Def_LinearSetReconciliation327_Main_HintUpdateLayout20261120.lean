-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLayout20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateLayout20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:51:32.126945+00:00
-- url     : https://prove2.me/theorems/663f6f8d-bf3e-48d5-aa6a-5e6eeb1e6e48
-- title:
--   LinearSetReconciliation327 — HintUpdateLayout (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateLayout20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateRoot20261120
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_9
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_10
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_4
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_6
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Theorems.Thm_LinearSetReconciliation327_Main_proposition_2_3
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
lemma zmod2_val_eq_ite (a : ZMod 2) : a.val = if a = 1 then 1 else 0 := by
  rcases zmod2_eq_zero_or_one a with h | h
  · rw [h]
    rw [if_neg zero_ne_one]
    exact ZMod.val_zero
  · rw [h]
    rw [if_pos rfl]
    exact ZMod.val_one 2
lemma zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have h := ZMod.val_lt a
  omega
lemma cr_sketch_singleton (CR : CRFamily) (N t a : ℕ) :
    CR.sketch N t ({a} : Finset ℕ) =
      (range (CR.rows N t)).filter (fun r => r ∈ CR.col N t a) := by
  ext r
  have hf : (({a} : Finset ℕ).filter (fun i => r ∈ CR.col N t i)) =
      if r ∈ CR.col N t a then ({a} : Finset ℕ) else ∅ := by
    ext i
    by_cases hi : i = a <;> by_cases h : r ∈ CR.col N t a <;> simp [hi, h]
  have hc : (({a} : Finset ℕ).filter (fun i => r ∈ CR.col N t i)).card =
      if r ∈ CR.col N t a then 1 else 0 := by
    rw [hf]
    by_cases h : r ∈ CR.col N t a <;> simp [h]
  rw [CRFamily.sketch, mem_filter, mem_filter, hc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    rw [if_neg h] at h2
    obtain ⟨k, hk⟩ := h2
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [if_pos h2]
    exact ⟨0, by norm_num⟩
lemma code_empty (sch : RowScheme) (j : Fin sch.m) (β : sch.Rand) (s : Fin sch.ℓ) :
    sch.code j β (∅ : Finset ℕ) s = 0 := by
  have h := sch.code_linear j β ∅ ∅ s
  rw [show symmDiff (∅ : Finset ℕ) ∅ = ∅ from by simp [symmDiff_def]] at h
  have h2 : sch.code j β (∅ : Finset ℕ) s + sch.code j β ∅ s = 0 := CharTwo.add_self_eq_zero _
  rw [h2] at h
  exact h
lemma rowImage_singleton {N m : ℕ} (π : Equiv.Perm (Fin N)) {a : ℕ} (ha : a < N) (j : ℕ) :
    rowImage N m π j ({a} : Finset ℕ) =
      (if (π ⟨a, ha⟩).val % m = j then {(π ⟨a, ha⟩).val / m} else ∅) := by
  classical
  ext v
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  by_cases hj : (π ⟨a, ha⟩).val % m = j
  · rw [if_pos hj, mem_singleton]
    constructor
    · rintro ⟨i, ⟨hi, hrow⟩, hv⟩
      have hia : i = ⟨a, ha⟩ := Fin.ext hi
      rw [hia] at hrow hv
      exact hv.symm
    · intro hv
      refine ⟨⟨a, ha⟩, ⟨rfl, hj⟩, ?_⟩
      exact hv.symm
  · rw [if_neg hj]
    constructor
    · rintro ⟨i, ⟨hi, hrow⟩, -⟩
      have hia : i = ⟨a, ha⟩ := Fin.ext hi
      rw [hia] at hrow
      exact absurd hrow hj
    · intro h
      exact absurd h (by simp)
def upItZero : UpIt := {}
def upDet (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) : ℕ → ℕ :=
  fun a =>
    if a = 0 then cnt
    else if a = 1 then W
    else if a = 2 then colBase
    else if a = 3 then 0
    else if colBase ≤ a then tab (a - colBase)
    else (items.getD ((a - 8) / 16) upItZero).fld ((a - 8) % 16)
@[simp] theorem upDet_one (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) :
    upDet cnt W colBase items tab 1 = W := by unfold upDet; simp
theorem upDet_tab (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) (a : ℕ)
    (h4 : 4 < a) (hcol : colBase ≤ a) :
    upDet cnt W colBase items tab a = tab (a - colBase) := by
  have h0 : a ≠ 0 := by omega
  have h1 : a ≠ 1 := by omega
  have h2 : a ≠ 2 := by omega
  have h3 : a ≠ 3 := by omega
  unfold upDet
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos hcol]
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
theorem upColIt_apply (E : RAMEnv) (i k m ell nmax base s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) (hbase : base < 2 ^ E.W)
    (hπ : E.perm k ab.c < 2 ^ E.W)
    (hbit : base + (E.perm k ab.c % m * ell + s) < 2 ^ E.W) :
    upvCn E i (upColIt k m ell nmax base s) ab = ab.c ∧
      upvFn E i (upColIt k m ell nmax base s) ab = ab.f ∧
      upvBit E i (upColIt k m ell nmax base s) ab
        = base + (E.perm k ab.c % m * ell + s) ∧
      upvWt E i (upColIt k m ell nmax base s) ab
        = upvCoin E i (upColIt k m ell nmax base s) ab % 2 ^ E.W := by
  have hM : 0 < 2 ^ E.W := pow_pos (by norm_num) _
  have hset0 : (upColIt k m ell nmax base s).setSt = 0 := rfl
  have hfrom0 : (upColIt k m ell nmax base s).fromI = 0 := rfl
  have hsrc0 : (upColIt k m ell nmax base s).srcC = 0 := rfl
  have hkp : (upColIt k m ell nmax base s).kp = k := rfl
  have hmit : (upColIt k m ell nmax base s).m = m := rfl
  have hellit : (upColIt k m ell nmax base s).ell = ell := rfl
  have hsit : (upColIt k m ell nmax base s).s = s := rfl
  have hbaseit : (upColIt k m ell nmax base s).base = base := rfl
  have hmode0 : (upColIt k m ell nmax base s).mode = 0 := rfl
  have huse1 : (upColIt k m ell nmax base s).useC = 1 := rfl
  have hZ1 : upvZ1 E (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ1, hkp]
  have hZ2 : upvZ2 E i (upColIt k m ell nmax base s) = 0 := by
    simp only [upvZ2, hfrom0, Nat.zero_mul, Nat.zero_mod]
  have hZ3 : upvZ3 E (upColIt k m ell nmax base s) = 1 := by
    simp only [upvZ3, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ4 : upvZ4 E (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ4, hZ1, hZ3, Nat.mul_one, Nat.mod_mod]
  have hZ5 : upvZ5 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ5, hZ4, hZ2, Nat.add_zero, Nat.mod_mod]
  have hZ6 : upvZ6 E (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvZ6, hsrc0, Nat.zero_mul, Nat.zero_mod]
  have hZ7 : upvZ7 E (upColIt k m ell nmax base s) = 1 := by
    simp only [upvZ7, hsrc0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ8 : upvZ8 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_one, Nat.mod_mod]
  have hImg : upvImg E i (upColIt k m ell nmax base s) ab = E.perm k ab.c := by
    simp only [upvImg, hZ8, hZ6, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hπ]
  have hltm : E.perm k ab.c % m < 2 ^ E.W := by
    have h := Nat.mod_lt (E.perm k ab.c) hm
    omega
  have hJ0 : upvJ0 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % m := by
    simp only [upvJ0, hImg, hmit, Nat.mod_eq_of_lt hltm]
  have hY1 : upvY1 E i (upColIt k m ell nmax base s) ab
      = (E.perm k ab.c % m + 2 ^ E.W - ab.c) % 2 ^ E.W := by
    simp only [upvY1, hJ0]
  have hY2 : upvY2 E i (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvY2, hset0, Nat.mul_zero, Nat.zero_mod]
  have hCn : upvCn E i (upColIt k m ell nmax base s) ab = ab.c := by
    simp only [upvCn, hY2, Nat.add_zero, Nat.mod_eq_of_lt hc]
  have hY11 : upvY11 E i (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvY11, hset0, Nat.mul_zero, Nat.zero_mod]
  have hFn : upvFn E i (upColIt k m ell nmax base s) ab = ab.f := by
    simp only [upvFn, hY11, Nat.add_zero, Nat.mod_eq_of_lt hf]
  have hellt : E.perm k ab.c % m * ell < 2 ^ E.W := by omega
  have hslt : E.perm k ab.c % m * ell + s < 2 ^ E.W := by omega
  have hY3 : upvY3 E i (upColIt k m ell nmax base s) ab
      = E.perm k ab.c % m * ell % 2 ^ E.W := by
    simp only [upvY3, hJ0, hellit]
  have hQ : upvQ E i (upColIt k m ell nmax base s) ab
      = (E.perm k ab.c % m * ell % 2 ^ E.W + s) % 2 ^ E.W := by
    simp only [upvQ, hY3, hsit]
  have hQv : upvQ E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % m * ell + s := by
    rw [hQ, Nat.mod_eq_of_lt hellt, Nat.mod_eq_of_lt hslt]
  have hX7 : upvX7 E i (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvX7, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hX8 : upvX8 E i (upColIt k m ell nmax base s) ab = base := by
    simp only [upvX8, hX7, hbaseit, Nat.zero_add, Nat.mod_eq_of_lt hbase]
  have hBit : upvBit E i (upColIt k m ell nmax base s) ab
      = base + (E.perm k ab.c % m * ell + s) := by
    rw [upvBit, hX8, hQv, Nat.mod_eq_of_lt hbit]
  have hX1 : upvX1 E (upColIt k m ell nmax base s) = 0 := by
    simp only [upvX1, huse1, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have hX2 : upvX2 E i (upColIt k m ell nmax base s) ab
      = upvCoin E i (upColIt k m ell nmax base s) ab % 2 ^ E.W := by
    simp only [upvX2, huse1, Nat.one_mul]
  have hW0 : upvW0 E i (upColIt k m ell nmax base s) ab
      = upvCoin E i (upColIt k m ell nmax base s) ab % 2 ^ E.W := by
    simp only [upvW0, hX2, hX1, Nat.add_zero, Nat.mod_mod]
  have hX10 : upvX10 E i (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvX10, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hWt : upvWt E i (upColIt k m ell nmax base s) ab
      = upvCoin E i (upColIt k m ell nmax base s) ab % 2 ^ E.W := by
    simp only [upvWt, hX10, hW0, Nat.zero_add, Nat.mod_mod]
  exact ⟨hCn, hFn, hBit, hWt⟩
theorem upCrIt_apply (E : RAMEnv) (i cidx stride base j : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (htb : stride * ab.c + cidx < 2 ^ E.W)
    (hj : stride * ab.c + cidx + j < 2 ^ E.W)
    (hjb : stride * ab.c + cidx + j + 1 < 2 ^ E.W)
    (helem : E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W + base < 2 ^ E.W)
    (hπ : E.perm 0 ab.c < 2 ^ E.W) :
    upvCn E i (upCrIt cidx stride base j) ab = ab.c ∧
      upvFn E i (upCrIt cidx stride base j) ab = ab.f ∧
      upvBit E i (upCrIt cidx stride base j) ab
        = base + E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W ∧
      upvWt E i (upCrIt cidx stride base j) ab
        = upvValid E i (upCrIt cidx stride base j) ab ∧
      upvValid E i (upCrIt cidx stride base j) ab
        = (if j < E.det (stride * ab.c + cidx) % 2 ^ E.W then 1 else 0) := by
  have hM : 0 < 2 ^ E.W := pow_pos (by norm_num) _
  have helem_lt : E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W < 2 ^ E.W := Nat.mod_lt _ hM
  have hset0 : (upCrIt cidx stride base j).setSt = 0 := rfl
  have hfrom0 : (upCrIt cidx stride base j).fromI = 0 := rfl
  have hsrc0 : (upCrIt cidx stride base j).srcC = 0 := rfl
  have hkp0 : (upCrIt cidx stride base j).kp = 0 := rfl
  have hm1 : (upCrIt cidx stride base j).m = 1 := rfl
  have hell1 : (upCrIt cidx stride base j).ell = 1 := rfl
  have hs0 : (upCrIt cidx stride base j).s = 0 := rfl
  have hbaseit : (upCrIt cidx stride base j).base = base := rfl
  have hmode1 : (upCrIt cidx stride base j).mode = 1 := rfl
  have huse0 : (upCrIt cidx stride base j).useC = 0 := rfl
  have hjit : (upCrIt cidx stride base j).sav = j := rfl
  have hstrit : (upCrIt cidx stride base j).stride = stride := rfl
  have hcid : (upCrIt cidx stride base j).cidx = cidx := rfl
  have hZ1 : upvZ1 E (upCrIt cidx stride base j) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ1, hkp0]
  have hZ2 : upvZ2 E i (upCrIt cidx stride base j) = 0 := by
    simp only [upvZ2, hfrom0, Nat.zero_mul, Nat.zero_mod]
  have hZ3 : upvZ3 E (upCrIt cidx stride base j) = 1 := by
    simp only [upvZ3, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ4 : upvZ4 E (upCrIt cidx stride base j) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ4, hZ1, hZ3, Nat.mul_one, Nat.mod_mod]
  have hZ5 : upvZ5 E i (upCrIt cidx stride base j) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ5, hZ4, hZ2, Nat.add_zero, Nat.mod_mod]
  have hZ6 : upvZ6 E (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvZ6, hsrc0, Nat.zero_mul, Nat.zero_mod]
  have hZ7 : upvZ7 E (upCrIt cidx stride base j) = 1 := by
    simp only [upvZ7, hsrc0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ8 : upvZ8 E i (upCrIt cidx stride base j) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_one, Nat.mod_mod]
  have hImg : upvImg E i (upCrIt cidx stride base j) ab = E.perm 0 ab.c := by
    simp only [upvImg, hZ8, hZ6, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hπ]
  have hJ0 : upvJ0 E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvJ0, hImg, hm1, Nat.mod_one, Nat.zero_mod]
  have hPos : upvPos E i (upCrIt cidx stride base j) ab = E.perm 0 ab.c := by
    simp only [upvPos, hImg, hm1, Nat.div_one, Nat.mod_eq_of_lt hπ]
  have hY2 : upvY2 E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvY2, hset0, Nat.mul_zero, Nat.zero_mod]
  have hCn : upvCn E i (upCrIt cidx stride base j) ab = ab.c := by
    simp only [upvCn, hY2, Nat.add_zero, Nat.mod_eq_of_lt hc]
  have hY11 : upvY11 E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvY11, hset0, Nat.mul_zero, Nat.zero_mod]
  have hFn : upvFn E i (upCrIt cidx stride base j) ab = ab.f := by
    simp only [upvFn, hY11, Nat.add_zero, Nat.mod_eq_of_lt hf]
  have hY3 : upvY3 E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvY3, hJ0, hell1, Nat.zero_mul, Nat.zero_mod]
  have hQ : upvQ E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvQ, hY3, hs0, Nat.zero_add, Nat.zero_mod]
  have hstride_lt : stride * ab.c < 2 ^ E.W := by omega
  have hX3 : upvX3 E i (upCrIt cidx stride base j) ab = stride * ab.c % 2 ^ E.W := by
    simp only [upvX3, hCn, hstrit]
  have hTb : upvTb E i (upCrIt cidx stride base j) ab = stride * ab.c + cidx := by
    rw [upvTb, hX3, hcid, Nat.mod_eq_of_lt hstride_lt, Nat.mod_eq_of_lt htb]
  have hCard : upvCard E i (upCrIt cidx stride base j) ab
      = E.det (stride * ab.c + cidx) % 2 ^ E.W := by
    simp only [upvCard, hTb]
  have hValid : upvValid E i (upCrIt cidx stride base j) ab
      = (if j < E.det (stride * ab.c + cidx) % 2 ^ E.W then 1 else 0) := by
    rw [upvValid, hCard, hjit]
    by_cases hv : j < E.det (stride * ab.c + cidx) % 2 ^ E.W
    · simp [hv, Nat.mod_eq_of_lt hW]
    · simp [hv]
  have hX4 : upvX4 E i (upCrIt cidx stride base j) ab = stride * ab.c + cidx + j := by
    rw [upvX4, hTb, hjit, Nat.mod_eq_of_lt hj]
  have hX5 : upvX5 E i (upCrIt cidx stride base j) ab = stride * ab.c + cidx + j + 1 := by
    rw [upvX5, hX4, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hjb]
  have hElem : upvElem E i (upCrIt cidx stride base j) ab
      = E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W := by
    simp only [upvElem, hX5]
  have hX6 : upvX6 E i (upCrIt cidx stride base j) ab
      = E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W := by
    rw [upvX6, hElem, hQ, Nat.sub_zero, add_mod_self, Nat.mod_eq_of_lt helem_lt]
  have hX7 : upvX7 E i (upCrIt cidx stride base j) ab
      = E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W := by
    simp only [upvX7, hmode1, Nat.mul_one, hX6, Nat.mod_eq_of_lt helem_lt]
  have hX8 : upvX8 E i (upCrIt cidx stride base j) ab
      = E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W + base := by
    rw [upvX8, hX7, hbaseit, Nat.mod_eq_of_lt helem]
  have hBit : upvBit E i (upCrIt cidx stride base j) ab
      = base + E.det (stride * ab.c + cidx + j + 1) % 2 ^ E.W := by
    rw [upvBit, hX8, hQ, Nat.add_zero, Nat.mod_eq_of_lt helem]
    omega
  have hX1 : upvX1 E (upCrIt cidx stride base j) = 1 := by
    simp only [upvX1, huse0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hX2 : upvX2 E i (upCrIt cidx stride base j) ab = 0 := by
    simp only [upvX2, huse0, Nat.zero_mul, Nat.zero_mod]
  have hW0 : upvW0 E i (upCrIt cidx stride base j) ab = 1 := by
    simp only [upvW0, hX2, hX1, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hX9 : upvX9 E i (upCrIt cidx stride base j) ab
      = (upvValid E i (upCrIt cidx stride base j) ab + 2 ^ E.W - 1) % 2 ^ E.W := by
    simp only [upvX9, hW0, Nat.mod_eq_of_lt hW]
  have hX10 : upvX10 E i (upCrIt cidx stride base j) ab
      = (upvValid E i (upCrIt cidx stride base j) ab + 2 ^ E.W - 1) % 2 ^ E.W := by
    simp only [upvX10, hmode1, Nat.mul_one, hX9, Nat.mod_mod]
  have hV : upvValid E i (upCrIt cidx stride base j) ab = 1 ∨
      upvValid E i (upCrIt cidx stride base j) ab = 0 := by
    rw [hValid]
    by_cases hv : j < E.det (stride * ab.c + cidx) % 2 ^ E.W <;> simp [hv]
  have hWt : upvWt E i (upCrIt cidx stride base j) ab
      = upvValid E i (upCrIt cidx stride base j) ab := by
    rw [upvWt, hX10, hW0]
    rcases hV with hV | hV
    · rw [hV, show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt hW]
    · rw [hV, Nat.zero_add, Nat.mod_eq_of_lt (show 2 ^ E.W - 1 < 2 ^ E.W by omega),
        show 2 ^ E.W - 1 + 1 = 2 ^ E.W by omega, Nat.mod_self]
  exact ⟨hCn, hFn, hBit, hWt, hValid⟩
def UpTabRec (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (N t toff : ℕ) : Prop :=
  ∀ c : ℕ, c < N →
    tab (toff + (Bc + 1) * c) = (CR.col N t c).card ∧
      ∀ q : ℕ, q < (CR.col N t c).card →
        tab (toff + (Bc + 1) * c + 1 + q) = ((CR.col N t c).sort (· ≤ ·)).getD q 0
theorem mem_image_range_sort (s : Finset ℕ) :
    (Finset.range s.card).image (fun q => (s.sort (· ≤ ·)).getD q 0) = s := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hlen : q < (s.sort (· ≤ ·)).length := by
      rw [Finset.length_sort (· ≤ ·)]
      exact hq
    rw [List.getD_eq_getElem _ 0 hlen]
    exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen)
  · intro hx
    obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hx)
    have hlen : q < (s.sort (· ≤ ·)).length := hq
    refine ⟨q, ?_, ?_⟩
    · rw [← Finset.length_sort (· ≤ ·)]
      exact hq
    · rw [List.getD_eq_getElem _ 0 hlen]
      exact hqe
theorem image_congr_range {f g : ℕ → ℕ} {n : ℕ} (h : ∀ q, q < n → f q = g q) :
    (Finset.range n).image f = (Finset.range n).image g := by
  ext y
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, (h q hq).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, h q hq⟩
def UpTabAt (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (toff N t : ℕ) : Prop :=
  ∀ c : ℕ, c < N →
    tab (toff + (Bc + 1) * c) = (CR.col N t c).card ∧
      (Finset.range (tab (toff + (Bc + 1) * c))).image
        (fun q => tab (toff + (Bc + 1) * c + 1 + q)) = CR.col N t c
theorem upTabAt_of_rec (CR : CRFamily) (Bc N t toff : ℕ) (tab : ℕ → ℕ)
    (h : UpTabRec CR Bc tab N t toff) : UpTabAt CR Bc tab toff N t := by
  intro c hc
  refine ⟨(h c hc).1, ?_⟩
  have himg := image_congr_range (n := (CR.col N t c).card)
    (f := fun q => tab (toff + (Bc + 1) * c + 1 + q))
    (g := fun q => ((CR.col N t c).sort (· ≤ ·)).getD q 0)
    (fun q hq => (h c hc).2 q hq)
  rw [(h c hc).1, himg, mem_image_range_sort]
theorem packSel_singleton (W q a : ℕ) (hW : 0 < W) :
    packSel W ({q} : Finset ℕ) a = if q / W = a then 2 ^ (q % W) else 0 := by
  unfold packSel
  by_cases h : q / W = a
  · rw [if_pos h, ← h]
    rw [ofBits, Finset.sum_eq_single (q % W)]
    · have hdm : q / W * W + q % W = q := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod q W
      simp [hdm]
    · intro b hb hne
      have hdm : q / W * W + q % W = q := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod q W
      have hne' : ¬ (q / W * W + b = q) := by omega
      simp [hne']
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.mod_lt q hW)) hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro b hb
    rw [Finset.mem_range] at hb
    have hne : ¬ (a * W + b = q) := by
      intro he
      apply h
      rw [← he, Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
    simp [hne]
def xorBit (W p w : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update mem (p / W) (mem (p / W) ^^^ (if w = 1 then 2 ^ (p % W) else 0))
theorem xorBit_apply (W p w : ℕ) (mem : ℕ → ℕ) (a : ℕ) :
    xorBit W p w mem a
      = if a = p / W then mem (p / W) ^^^ (if w = 1 then 2 ^ (p % W) else 0) else mem a := by
  unfold xorBit
  exact Function.update_apply _ _ _ _
theorem xorBit_zero (W p : ℕ) (mem : ℕ → ℕ) : xorBit W p 0 mem = mem := by
  funext a
  rw [xorBit_apply]
  by_cases ha : a = p / W
  · rw [if_pos ha]
    simp [ha]
  · rw [if_neg ha]
theorem xorBit_lt (W p w : ℕ) (mem : ℕ → ℕ) (hW : 0 < W) (hWlt : W < 2 ^ W)
    (hp : p < 2 ^ W) (hw : w = 0 ∨ w = 1) (hmem : ∀ x, mem x < 2 ^ W) (a : ℕ) :
    xorBit W p w mem a < 2 ^ W := by
  rw [xorBit_apply]
  by_cases ha : a = p / W
  · rw [if_pos ha]
    have h1 : mem (p / W) < 2 ^ W := hmem _
    have h2 : (if w = 1 then 2 ^ (p % W) else 0) < 2 ^ W := by
      rcases hw with h | h
      · rw [if_neg (by omega)]
        exact Nat.two_pow_pos W
      · rw [if_pos h]
        exact Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt p hW)
    exact Nat.xor_lt_two_pow h1 h2
  · rw [if_neg ha]
    exact hmem a
theorem upvWi_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hp : upvBit E i it ab < 2 ^ E.W) :
    upvWi E i it ab = upvBit E i it ab / E.W := by
  unfold upvWi upvWw
  rw [hWw, Nat.mod_eq_of_lt (by have h := Nat.div_le_self (upvBit E i it ab) E.W; omega)]
theorem upvB1_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W) (hp : upvBit E i it ab < 2 ^ E.W) :
    upvB1 E i it ab = upvBit E i it ab % E.W := by
  unfold upvB1 upvWw
  rw [hWw, Nat.mod_eq_of_lt (by have h := Nat.mod_lt (upvBit E i it ab) hWpos; omega)]
theorem upvSh_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W) (hp : upvBit E i it ab < 2 ^ E.W) :
    upvSh E i it ab = 2 ^ (upvBit E i it ab % E.W) := by
  unfold upvSh
  rw [upvB1_eq E i it ab hWpos hWlt hWw hp]
  have h1 : 1 % 2 ^ E.W = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.one_mul]
  exact Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt (upvBit E i it ab) hWpos))
theorem upvMask0_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hwtf : upvWt E i it ab * upvFn E i it ab < 2 ^ E.W)
    (hmul : upvWt E i it ab * upvFn E i it ab * it.mOn < 2 ^ E.W) :
    upvMask0 E i it ab = upvWt E i it ab * upvFn E i it ab * it.mOn := by
  unfold upvMask0 upvX11
  rw [Nat.mod_eq_of_lt hwtf, Nat.mod_eq_of_lt hmul]
theorem upvMask_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hp : upvBit E i it ab < 2 ^ E.W)
    (hwtf : upvWt E i it ab * upvFn E i it ab < 2 ^ E.W)
    (hmul : upvWt E i it ab * upvFn E i it ab * it.mOn < 2 ^ E.W)
    (hmul2 : upvWt E i it ab * upvFn E i it ab * it.mOn < 2) :
    upvMask E i it ab
      = upvWt E i it ab * upvFn E i it ab * it.mOn * 2 ^ (upvBit E i it ab % E.W) := by
  unfold upvMask
  rw [upvMask0_eq E i it ab hwtf hmul, upvSh_eq E i it ab hWpos hWlt hWw hp]
  refine Nat.mod_eq_of_lt ?_
  have h2 : 2 ^ (upvBit E i it ab % E.W) < 2 ^ E.W :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt (upvBit E i it ab) hWpos)
  calc upvWt E i it ab * upvFn E i it ab * it.mOn * 2 ^ (upvBit E i it ab % E.W)
      ≤ 1 * 2 ^ (upvBit E i it ab % E.W) := by
        refine Nat.mul_le_mul_right _ ?_
        omega
    _ = 2 ^ (upvBit E i it ab % E.W) := Nat.one_mul _
    _ < 2 ^ E.W := h2
theorem upvOld_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hp : upvBit E i it ab < 2 ^ E.W) (hmem : ∀ x, ab.mem x < 2 ^ E.W) :
    upvOld E i it ab = ab.mem (upvBit E i it ab / E.W) := by
  unfold upvOld
  rw [upvWi_eq E i it ab hWpos hWw hp, Nat.mod_eq_of_lt (hmem _)]
theorem upvNew_eq (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hp : upvBit E i it ab < 2 ^ E.W)
    (hwtf : upvWt E i it ab * upvFn E i it ab < 2 ^ E.W)
    (hmul : upvWt E i it ab * upvFn E i it ab * it.mOn < 2 ^ E.W)
    (hmul2 : upvWt E i it ab * upvFn E i it ab * it.mOn < 2)
    (hmem : ∀ x, ab.mem x < 2 ^ E.W) :
    upvNew E i it ab
      = ab.mem (upvBit E i it ab / E.W)
        ^^^ (upvWt E i it ab * upvFn E i it ab * it.mOn * 2 ^ (upvBit E i it ab % E.W)) := by
  unfold upvNew
  rw [upvOld_eq E i it ab hWpos hWw hp hmem, upvMask_eq E i it ab hWpos hWlt hWw hp hwtf hmul hmul2]
  refine Nat.mod_eq_of_lt ?_
  refine Nat.xor_lt_two_pow (hmem _) ?_
  have h2 : 2 ^ (upvBit E i it ab % E.W) < 2 ^ E.W :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt (upvBit E i it ab) hWpos)
  calc upvWt E i it ab * upvFn E i it ab * it.mOn * 2 ^ (upvBit E i it ab % E.W)
      ≤ 1 * 2 ^ (upvBit E i it ab % E.W) := by
        refine Nat.mul_le_mul_right _ ?_
        omega
    _ = 2 ^ (upvBit E i it ab % E.W) := Nat.one_mul _
    _ < 2 ^ E.W := h2
theorem upApply_mem (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W) (hm : it.mode < 2)
    (hp : upvBit E i it ab < 2 ^ E.W)
    (hwtf : upvWt E i it ab * upvFn E i it ab < 2 ^ E.W)
    (hmul : upvWt E i it ab * upvFn E i it ab * it.mOn < 2 ^ E.W)
    (hmul2 : upvWt E i it ab * upvFn E i it ab * it.mOn < 2)
    (hmem : ∀ x, ab.mem x < 2 ^ E.W) :
    (upApply E i it ab).mem
      = xorBit E.W (upvBit E i it ab) (upvWt E i it ab * upvFn E i it ab * it.mOn) ab.mem := by
  have hW1 : 1 < 2 ^ E.W := by
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hWpos
    simpa using this
  rw [upApply_eq_body E i it ab hW1 hm hmem]
  have h1 : (upApplyBody E i it ab).mem
      = Function.update ab.mem (upvWi E i it ab) (upvNew E i it ab) := rfl
  rw [h1, upvWi_eq E i it ab hWpos hWw hp,
    upvNew_eq E i it ab hWpos hWlt hWw hp hwtf hmul hmul2 hmem]
  funext a
  rw [Function.update_apply, xorBit_apply]
  by_cases ha : a = upvBit E i it ab / E.W
  · simp only [if_pos ha]
    have hw01 : upvWt E i it ab * upvFn E i it ab * it.mOn = 0
        ∨ upvWt E i it ab * upvFn E i it ab * it.mOn = 1 := by omega
    rcases hw01 with h | h <;> simp [h]
  · simp only [if_neg ha]
def foldTog (W : ℕ) : (ℕ → ℕ) → List (ℕ × ℕ) → (ℕ → ℕ)
  | mem, [] => mem
  | mem, q :: rest => foldTog W (xorBit W q.1 q.2 mem) rest
def activeBits (L : List (ℕ × ℕ)) : List ℕ :=
  (L.filter (fun q => q.2 = 1)).map (fun q => q.1)
theorem activeBits_cons_zero (p : ℕ) (rest : List (ℕ × ℕ)) :
    activeBits ((p, 0) :: rest) = activeBits rest := by
  simp [activeBits]
theorem activeBits_cons_one (p : ℕ) (rest : List (ℕ × ℕ)) :
    activeBits ((p, 1) :: rest) = p :: activeBits rest := by
  simp [activeBits]
theorem activeBits_subset {rest : List (ℕ × ℕ)} {b : ℕ} (hb : b ∈ activeBits rest) :
    b ∈ rest.map Prod.fst := by
  simp only [activeBits, List.mem_map, List.mem_filter] at hb ⊢
  obtain ⟨q, ⟨hq, -⟩, rfl⟩ := hb
  exact ⟨q, hq, rfl⟩
theorem foldTog_packSel (W : ℕ) (hW : 0 < W) (hWlt : W < 2 ^ W) (mem : ℕ → ℕ)
    (hmem : ∀ x, mem x < 2 ^ W) (L : List (ℕ × ℕ))
    (hwt : ∀ q ∈ L, q.2 = 0 ∨ q.2 = 1)
    (hbit : ∀ q ∈ L, q.1 < 2 ^ W)
    (hnd : (L.map Prod.fst).Nodup) (a : ℕ) :
    foldTog W mem L a = mem a ^^^ packSel W (activeBits L).toFinset a := by
  induction L generalizing mem with
  | nil => simp [foldTog, activeBits, packSel_empty]
  | cons q rest ih =>
      obtain ⟨p, w⟩ := q
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hpnot, hndrest⟩ := hnd
      have hmem' : ∀ x, xorBit W p w mem x < 2 ^ W := fun x =>
        xorBit_lt W p w mem hW hWlt (hbit (p, w) (List.mem_cons_self ..))
          (hwt (p, w) (List.mem_cons_self ..)) hmem x
      rw [foldTog, ih (xorBit W p w mem) hmem'
        (fun r hr => hwt r (List.mem_cons_of_mem _ hr))
        (fun r hr => hbit r (List.mem_cons_of_mem _ hr)) hndrest]
      have hw01 : w = 0 ∨ w = 1 := hwt (p, w) (List.mem_cons_self ..)
      rcases hw01 with hw | hw
      ·
        rw [hw, activeBits_cons_zero, xorBit_zero]
      ·
        rw [hw, activeBits_cons_one, xorBit_apply]
        have hpin : p ∉ (activeBits rest).toFinset := by
          rw [List.mem_toFinset]
          intro hb
          exact hpnot (activeBits_subset hb)
        have hdisj : Disjoint ({p} : Finset ℕ) (activeBits rest).toFinset := by
          refine Finset.disjoint_left.mpr ?_
          intro x hx hx'
          rw [Finset.mem_singleton] at hx
          rw [hx] at hx'
          exact hpin hx'
        rw [List.toFinset_cons, Finset.insert_eq,
          packSel_union W hdisj a, packSel_singleton W p a hW]
        by_cases ha : a = p / W
        · subst ha
          rw [if_pos rfl, if_pos rfl, if_pos rfl, Nat.xor_assoc]
        · rw [if_neg ha, if_neg (fun h => ha h.symm), Nat.zero_xor]
theorem upvBit_mem_irrel (E : RAMEnv) (i : ℕ) (it : UpIt) (c f : ℕ) (m m' : ℕ → ℕ) :
    upvBit E i it (⟨m, c, f⟩ : UpAbs) = upvBit E i it (⟨m', c, f⟩ : UpAbs) := rfl
theorem upvWt_mem_irrel (E : RAMEnv) (i : ℕ) (it : UpIt) (c f : ℕ) (m m' : ℕ → ℕ) :
    upvWt E i it (⟨m, c, f⟩ : UpAbs) = upvWt E i it (⟨m', c, f⟩ : UpAbs) := rfl
theorem upvCn_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (h0 : it.setSt = 0) (hc : ab.c < 2 ^ E.W) :
    upvCn E i it ab = ab.c := by
  unfold upvCn upvY2
  rw [h0, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hc]
theorem upvFn_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (h0 : it.setSt = 0) (hf : ab.f < 2 ^ E.W) :
    upvFn E i it ab = ab.f := by
  unfold upvFn upvY11
  rw [h0, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hf]
theorem upFold_fixed (E : RAMEnv) (i : ℕ) (c f : ℕ) (L : List UpIt)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W)
    (hfix : ∀ it ∈ L, it.setSt = 0 ∧ it.mode < 2)
    (hbit : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvBit E i it (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W)
    (hwtf : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W)
    (hmul : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 ^ E.W)
    (hmul2 : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2) :
    ∀ (mem : ℕ → ℕ), (∀ x, mem x < 2 ^ E.W) →
      upFold E i (⟨mem, c, f⟩ : UpAbs) L
        = ⟨foldTog E.W mem (L.map (fun it =>
              (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs),
               upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn))), c, f⟩ := by
  revert hfix hbit hwtf hmul hmul2
  induction L with
  | nil => intro _ _ _ _ _ mem _; rfl
  | cons it rest ih =>
      intro hfix hbit hwtf hmul hmul2 mem hmem
      have hset : it.setSt = 0 := (hfix it (List.mem_cons_self ..)).1
      have hmode : it.mode < 2 := (hfix it (List.mem_cons_self ..)).2
      have hW1 : 1 < 2 ^ E.W := by
        have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hWpos
        simpa using this
      have hp : upvBit E i it (⟨mem, c, f⟩ : UpAbs) < 2 ^ E.W :=
        hbit it (List.mem_cons_self ..) mem
      have hf0 : upvFn E i it (⟨mem, c, f⟩ : UpAbs) = f :=
        upvFn_setSt0 E i it _ hset hf
      have hcn : upvCn E i it (⟨mem, c, f⟩ : UpAbs) = c :=
        upvCn_setSt0 E i it _ hset hc
      have hp' : upvBit E i it (⟨mem, c, f⟩ : UpAbs)
          = upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs) := upvBit_mem_irrel E i it c f mem _
      have hw' : upvWt E i it (⟨mem, c, f⟩ : UpAbs)
          = upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) := upvWt_mem_irrel E i it c f mem _
      have hwtf' : upvWt E i it (⟨mem, c, f⟩ : UpAbs) * upvFn E i it (⟨mem, c, f⟩ : UpAbs)
          < 2 ^ E.W := by rw [hf0]; exact hwtf it (List.mem_cons_self ..) mem
      have hmul' : upvWt E i it (⟨mem, c, f⟩ : UpAbs) * upvFn E i it (⟨mem, c, f⟩ : UpAbs)
          * it.mOn < 2 ^ E.W := by rw [hf0]; exact hmul it (List.mem_cons_self ..) mem
      have hmul2' : upvWt E i it (⟨mem, c, f⟩ : UpAbs) * upvFn E i it (⟨mem, c, f⟩ : UpAbs)
          * it.mOn < 2 := by rw [hf0]; exact hmul2 it (List.mem_cons_self ..) mem
      have hstep : upApply E i it (⟨mem, c, f⟩ : UpAbs)
          = ⟨xorBit E.W (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs))
              (upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn) mem, c, f⟩ := by
        have hm' : (upApply E i it (⟨mem, c, f⟩ : UpAbs)).mem
            = xorBit E.W (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs))
                (upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn) mem := by
          have h := upApply_mem E i it (⟨mem, c, f⟩ : UpAbs) hWpos hWlt hWw hmode hp hwtf'
            hmul' hmul2' hmem
          rw [hp', hw', hf0] at h
          exact h
        have heq : upApply E i it (⟨mem, c, f⟩ : UpAbs)
            = upApplyBody E i it (⟨mem, c, f⟩ : UpAbs) :=
          upApply_eq_body E i it _ hW1 hmode hmem
        have hcn' : (upApply E i it (⟨mem, c, f⟩ : UpAbs)).c = c := by rw [heq]; exact hcn
        have hf0' : (upApply E i it (⟨mem, c, f⟩ : UpAbs)).f = f := by rw [heq]; exact hf0
        show (⟨(upApply E i it (⟨mem, c, f⟩ : UpAbs)).mem,
               (upApply E i it (⟨mem, c, f⟩ : UpAbs)).c,
               (upApply E i it (⟨mem, c, f⟩ : UpAbs)).f⟩ : UpAbs)
          = ⟨xorBit E.W (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs))
              (upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn) mem, c, f⟩
        rw [hm', hcn', hf0']
      have hbit_r : ∀ it' ∈ rest, ∀ m : ℕ → ℕ,
          upvBit E i it' (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W :=
        fun it' hit' m => hbit it' (List.mem_cons_of_mem _ hit') m
      have hwtf_r : ∀ it' ∈ rest, ∀ m : ℕ → ℕ,
          upvWt E i it' (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W :=
        fun it' hit' m => hwtf it' (List.mem_cons_of_mem _ hit') m
      have hmul_r : ∀ it' ∈ rest, ∀ m : ℕ → ℕ,
          upvWt E i it' (⟨m, c, f⟩ : UpAbs) * f * it'.mOn < 2 ^ E.W :=
        fun it' hit' m => hmul it' (List.mem_cons_of_mem _ hit') m
      have hmul2_r : ∀ it' ∈ rest, ∀ m : ℕ → ℕ,
          upvWt E i it' (⟨m, c, f⟩ : UpAbs) * f * it'.mOn < 2 :=
        fun it' hit' m => hmul2 it' (List.mem_cons_of_mem _ hit') m
      have hfix_r : ∀ it' ∈ rest, it'.setSt = 0 ∧ it'.mode < 2 :=
        fun it' hit' => hfix it' (List.mem_cons_of_mem _ hit')
      have hw2 : upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn < 2 :=
        hmul2 it (List.mem_cons_self ..) (fun _ => 0)
      have hw01 : upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn = 0
          ∨ upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn = 1 := by omega
      have hbit0 : upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs) < 2 ^ E.W :=
        hbit it (List.mem_cons_self ..) (fun _ => 0)
      have hmem' : ∀ x, xorBit E.W (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs))
          (upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn) mem x < 2 ^ E.W := fun x =>
        xorBit_lt E.W _ _ mem hWpos hWlt hbit0 hw01 hmem x
      rw [upFold, hstep, ih hfix_r hbit_r hwtf_r hmul_r hmul2_r _ hmem']
      simp only [List.map_cons, foldTog]
theorem xorBit_of_ne_one (W p w : ℕ) (mem : ℕ → ℕ) (h : w ≠ 1) : xorBit W p w mem = mem := by
  funext a
  rw [xorBit_apply]
  by_cases ha : a = p / W
  · rw [if_pos ha, if_neg h, Nat.xor_zero, ha]
  · rw [if_neg ha]
theorem foldTog_filter_one (W : ℕ) (mem : ℕ → ℕ) (L : List (ℕ × ℕ)) :
    foldTog W mem L = foldTog W mem (L.filter (fun q => q.2 = 1)) := by
  induction L generalizing mem with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨p, w⟩ := q
      simp only [foldTog, List.filter_cons]
      by_cases hw : w = 1
      · rw [if_pos (by simpa using hw)]
        exact ih (xorBit W p w mem)
      · rw [if_neg (by simpa using hw), xorBit_of_ne_one W p w mem hw]
        exact ih mem
theorem foldTog_packSel_active (W : ℕ) (hW : 0 < W) (hWlt : W < 2 ^ W) (mem : ℕ → ℕ)
    (hmem : ∀ x, mem x < 2 ^ W) (L : List (ℕ × ℕ))
    (hwt : ∀ q ∈ L, q.2 = 0 ∨ q.2 = 1)
    (hbit : ∀ q ∈ L, q.1 < 2 ^ W) (hnd : (activeBits L).Nodup) (a : ℕ) :
    foldTog W mem L a = mem a ^^^ packSel W (activeBits L).toFinset a := by
  have hact : activeBits (L.filter (fun q => q.2 = 1)) = activeBits L := by
    unfold activeBits
    rw [List.filter_filter]
    simp only [Bool.and_self]
  have hwt' : ∀ q ∈ L.filter (fun q => q.2 = 1), q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    rw [List.mem_filter] at hq
    exact Or.inr (of_decide_eq_true hq.2)
  have hbit' : ∀ q ∈ L.filter (fun q => q.2 = 1), q.1 < 2 ^ W := by
    intro q hq
    rw [List.mem_filter] at hq
    exact hbit q hq.1
  have hnd' : ((L.filter (fun q => q.2 = 1)).map Prod.fst).Nodup := by
    simpa [activeBits] using hnd
  calc foldTog W mem L a
      = foldTog W mem (L.filter (fun q => q.2 = 1)) a := by rw [foldTog_filter_one]
    _ = mem a ^^^ packSel W (activeBits (L.filter (fun q => q.2 = 1))).toFinset a :=
        foldTog_packSel W hW hWlt mem hmem _ hwt' hbit' hnd' a
    _ = mem a ^^^ packSel W (activeBits L).toFinset a := by rw [hact]
def upPairs (E : RAMEnv) (i c f : ℕ) (L : List UpIt) : List (ℕ × ℕ) :=
  L.map (fun it =>
    (upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs),
     upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs) * f * it.mOn))
theorem upFold_own (E : RAMEnv) (i c f : ℕ) (L : List UpIt)
    (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W)
    (hfix : ∀ it ∈ L, it.setSt = 0 ∧ it.mode < 2)
    (hbit : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvBit E i it (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W)
    (hwtf : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W)
    (hmul : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 ^ E.W)
    (hmul2 : ∀ it ∈ L, ∀ m : ℕ → ℕ, upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2)
    (hwt : ∀ q ∈ upPairs E i c f L, q.2 = 0 ∨ q.2 = 1)
    (hbitq : ∀ q ∈ upPairs E i c f L, q.1 < 2 ^ E.W)
    (hnd : (activeBits (upPairs E i c f L)).Nodup)
    (mem : ℕ → ℕ) (hmem : ∀ x, mem x < 2 ^ E.W) (a : ℕ) :
    (upFold E i (⟨mem, c, f⟩ : UpAbs) L).mem a
        = mem a ^^^ packSel E.W (activeBits (upPairs E i c f L)).toFinset a ∧
      (upFold E i (⟨mem, c, f⟩ : UpAbs) L).c = c ∧
      (upFold E i (⟨mem, c, f⟩ : UpAbs) L).f = f := by
  have h := upFold_fixed E i c f L hWpos hWlt hWw hc hf hfix hbit hwtf hmul hmul2 mem hmem
  have h' : upFold E i (⟨mem, c, f⟩ : UpAbs) L
      = ⟨foldTog E.W mem (upPairs E i c f L),  c, f⟩ := h
  rw [h']
  exact ⟨foldTog_packSel_active E.W hWpos hWlt mem hmem (upPairs E i c f L) hwt hbitq hnd a,
    rfl, rfl⟩
theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β}
    (h : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy])) hl.2⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨b, hb, hba⟩ := hmem
      have hab : a = b := h a (by simp) b (by simp [hb]) hba.symm
      exact hl.1 (hab ▸ hb)
theorem upColBits_ne_crBit {m ell base j0 : ℕ} (hj0 : j0 < m) {s : ℕ} (hs : s < ell) (e : ℕ) :
    base + (j0 * ell + s) ≠ base + m * ell + e := by
  intro h
  have h1 : j0 * ell + s < m * ell := by
    calc j0 * ell + s < j0 * ell + ell := by omega
      _ = (j0 + 1) * ell := by rw [Nat.succ_mul]
      _ ≤ m * ell := Nat.mul_le_mul_right ell (by omega)
  omega
theorem upTabAt_inj (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (toff N t c : ℕ)
    (hAt : UpTabAt CR Bc tab toff N t) (hc : c < N) :
    ∀ j j', j < (CR.col N t c).card → j' < (CR.col N t c).card →
      tab (toff + (Bc + 1) * c + 1 + j) = tab (toff + (Bc + 1) * c + 1 + j') → j = j' := by
  obtain ⟨hcard, him⟩ := hAt c hc
  have him' : (Finset.range (CR.col N t c).card).image
      (fun q => tab (toff + (Bc + 1) * c + 1 + q)) = CR.col N t c := by
    rw [← hcard]
    exact him
  have hinj : Set.InjOn (fun q => tab (toff + (Bc + 1) * c + 1 + q))
      ↑(Finset.range (CR.col N t c).card) := by
    apply Finset.injOn_of_card_image_eq
    rw [him']
    simp
  intro j j' hj hj' he
  exact hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hj')) he
theorem filter_congr_list {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.filter_cons, List.filter_cons, h a (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
theorem map_congr_list {α β : Type} {l : List α} {f g : α → β} (h : ∀ a ∈ l, f a = g a) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.map_cons, List.map_cons, h a (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
theorem range_filter_lt : ∀ (Bc card : ℕ), card ≤ Bc →
    (List.range Bc).filter (fun j => j < card) = List.range card := by
  intro Bc
  induction Bc with
  | zero =>
      intro card h
      have h0 : card = 0 := by omega
      subst h0
      rfl
  | succ n ih =>
      intro card h
      rw [List.range_succ, List.filter_append]
      by_cases hlt : n < card
      · have hc : card = n + 1 := by omega
        rw [hc]
        have hkeep : (List.range n).filter (fun j => j < n + 1) = List.range n := by
          rw [List.filter_eq_self]
          intro a ha
          simp only [List.mem_range] at ha
          exact decide_eq_true (by omega)
        have hlast : ([n] : List ℕ).filter (fun j => j < n + 1) = [n] := by
          rw [List.filter_eq_self]
          intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          exact decide_eq_true (by omega)
        rw [hkeep, hlast, List.range_succ]
      · have hle : card ≤ n := by omega
        rw [ih card hle]
        have hnil : ([n] : List ℕ).filter (fun j => j < card) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          rw [decide_eq_false (by omega : ¬ (a < card))]
          simp
        rw [hnil, List.append_nil]
theorem activeBits_append (l₁ l₂ : List (ℕ × ℕ)) :
    activeBits (l₁ ++ l₂) = activeBits l₁ ++ activeBits l₂ := by
  unfold activeBits
  rw [List.filter_append, List.map_append]
theorem upPairs_append (E : RAMEnv) (i c f : ℕ) (l₁ l₂ : List UpIt) :
    upPairs E i c f (l₁ ++ l₂) = upPairs E i c f l₁ ++ upPairs E i c f l₂ := by
  unfold upPairs
  rw [List.map_append]
theorem upPairs_map (E : RAMEnv) (i c f : ℕ) (L : List ℕ) (F : ℕ → UpIt) :
    upPairs E i c f (L.map F) = L.map (fun j =>
      (upvBit E i (F j) (⟨fun _ => 0, c, f⟩ : UpAbs),
       upvWt E i (F j) (⟨fun _ => 0, c, f⟩ : UpAbs) * f * (F j).mOn)) := by
  unfold upPairs
  rw [List.map_map]
  rfl
theorem activeBits_map₂ {α : Type} (L : List α) (bit wt : α → ℕ) :
    activeBits (L.map (fun a => (bit a, wt a)))
      = (L.filter (fun a => wt a = 1)).map bit := by
  unfold activeBits
  induction L with
  | nil => rfl
  | cons a rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases h : wt a = 1
      · rw [if_pos (by simp [h]), if_pos (by simp [h]), List.map_cons, List.map_cons, ih]
      · rw [if_neg (by simp [h]), if_neg (by simp [h]), ih]
theorem nodup_append_list {l₁ l₂ : List ℕ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a rest ih =>
      rw [List.cons_append, List.nodup_cons]
      rw [List.nodup_cons] at h₁
      refine ⟨?_, ih h₁.2 (fun x hx b hb => hd x (List.mem_cons_of_mem _ hx) b hb)⟩
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with h | h
      · exact h₁.1 h
      · exact hd a (List.mem_cons_self ..) a h rfl
theorem activeBits_ownCr (CR : CRFamily) (E : RAMEnv) (i c κ N t base toff Bc : ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hperm : E.perm 0 c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (htb : (Bc + 1) * c + (κ + toff) < 2 ^ E.W)
    (hjB : (Bc + 1) * c + (κ + toff) + Bc < 2 ^ E.W)
    (hjbB : (Bc + 1) * c + (κ + toff) + Bc + 1 < 2 ^ E.W)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (hcard : E.det ((Bc + 1) * c + (κ + toff)) % 2 ^ E.W = (CR.col N t c).card)
    (hcardB : (CR.col N t c).card ≤ Bc) :
    activeBits (upPairs E i c 1 ((List.range Bc).map (fun j => upCrIt (κ + toff) (Bc + 1) base j)))
      = (List.range (CR.col N t c).card).map
          (fun j => base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W) := by
  have hwt : ∀ j ∈ List.range Bc,
      upvWt E i (upCrIt (κ + toff) (Bc + 1) base j) (⟨fun _ => 0, c, 1⟩ : UpAbs)
        = (if j < (CR.col N t c).card then 1 else 0) := by
    intro j hj
    have hjB' : j < Bc := List.mem_range.mp hj
    have hjc : (Bc + 1) * c + (κ + toff) + j < 2 ^ E.W := by omega
    have hjbc : (Bc + 1) * c + (κ + toff) + j + 1 < 2 ^ E.W := by omega
    have hele : E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W + base < 2 ^ E.W := by
      have h := helemB j hjB'
      omega
    obtain ⟨-, -, -, hWt, hVal⟩ :=
      upCrIt_apply E i (κ + toff) (Bc + 1) base j (⟨fun _ => 0, c, 1⟩ : UpAbs) hW hc
        hW hbase htb hjc hjbc hele hperm
    rw [hWt, hVal, hcard]
  have hbit : ∀ j ∈ List.range Bc,
      upvBit E i (upCrIt (κ + toff) (Bc + 1) base j) (⟨fun _ => 0, c, 1⟩ : UpAbs)
        = base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W := by
    intro j hj
    have hjB' : j < Bc := List.mem_range.mp hj
    have hjc : (Bc + 1) * c + (κ + toff) + j < 2 ^ E.W := by omega
    have hjbc : (Bc + 1) * c + (κ + toff) + j + 1 < 2 ^ E.W := by omega
    have hele : E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W + base < 2 ^ E.W := by
      have h := helemB j hjB'
      omega
    obtain ⟨-, -, hBit, -, -⟩ :=
      upCrIt_apply E i (κ + toff) (Bc + 1) base j (⟨fun _ => 0, c, 1⟩ : UpAbs) hW hc
        hW hbase htb hjc hjbc hele hperm
    exact hBit
  have hP : ∀ j ∈ List.range Bc,
      (decide (upvWt E i (upCrIt (κ + toff) (Bc + 1) base j) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
        * (upCrIt (κ + toff) (Bc + 1) base j).mOn = 1)
        = decide (j < (CR.col N t c).card)) := by
    intro j hj
    have hmOn : (upCrIt (κ + toff) (Bc + 1) base j).mOn = 1 := rfl
    rw [hwt j hj, hmOn]
    by_cases hjc : j < (CR.col N t c).card
    · simp [hjc]
    · simp [hjc]
  rw [upPairs_map]
  refine Eq.trans (activeBits_map₂ (List.range Bc)
    (fun j => upvBit E i (upCrIt (κ + toff) (Bc + 1) base j) (⟨fun _ => 0, c, 1⟩ : UpAbs))
    (fun j => upvWt E i (upCrIt (κ + toff) (Bc + 1) base j) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
      * (upCrIt (κ + toff) (Bc + 1) base j).mOn)) ?_
  rw [filter_congr_list hP, range_filter_lt Bc (CR.col N t c).card hcardB]
  refine map_congr_list (fun j hj => hbit j (List.mem_range.mpr ?_))
  have := List.mem_range.mp hj
  omega
theorem nodup_activeBits_ownCr (CR : CRFamily) (E : RAMEnv) (i c κ N t base toff Bc : ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hperm : E.perm 0 c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (htb : (Bc + 1) * c + (κ + toff) < 2 ^ E.W)
    (hjB : (Bc + 1) * c + (κ + toff) + Bc < 2 ^ E.W)
    (hjbB : (Bc + 1) * c + (κ + toff) + Bc + 1 < 2 ^ E.W)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (hcard : E.det ((Bc + 1) * c + (κ + toff)) % 2 ^ E.W = (CR.col N t c).card)
    (hcardB : (CR.col N t c).card ≤ Bc)
    (hinj : ∀ j j', j < (CR.col N t c).card → j' < (CR.col N t c).card →
      E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W
        = E.det ((Bc + 1) * c + (κ + toff) + j' + 1) % 2 ^ E.W → j = j') :
    (activeBits (upPairs E i c 1
      ((List.range Bc).map (fun j => upCrIt (κ + toff) (Bc + 1) base j)))).Nodup := by
  rw [activeBits_ownCr CR E i c κ N t base toff Bc hW hc hperm hbase htb hjB hjbB helemB hcard
    hcardB]
  refine nodup_map_of_inj ?_ List.nodup_range
  intro j hj j' hj' he
  rw [List.mem_range] at hj hj'
  exact hinj j j' hj hj' (Nat.add_left_cancel he)
theorem activeBits_ownDirectCol (E : RAMEnv) (i c k m ell nmax base : ℕ)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hperm : E.perm k c < 2 ^ E.W)
    (hbit : ∀ s, s < ell → base + (E.perm k c % m * ell + s) < 2 ^ E.W) :
    activeBits (upPairs E i c 1 ((List.range ell).map (fun s => upColIt k m ell nmax base s)))
      = ((List.range ell).filter (fun s =>
            upvWt E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
              * (upColIt k m ell nmax base s).mOn = 1)).map
          (fun s => base + (E.perm k c % m * ell + s)) := by
  have hbitq : ∀ s ∈ List.range ell,
      upvBit E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs)
        = base + (E.perm k c % m * ell + s) := by
    intro s hs
    obtain ⟨-, -, hBit, -⟩ :=
      upColIt_apply E i k m ell nmax base s (⟨fun _ => 0, c, 1⟩ : UpAbs) hW hm hmM hc hW hbase hperm
        (hbit s (List.mem_range.mp hs))
    exact hBit
  rw [upPairs_map]
  refine Eq.trans (activeBits_map₂ (List.range ell)
    (fun s => upvBit E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs))
    (fun s => upvWt E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
      * (upColIt k m ell nmax base s).mOn)) ?_
  exact map_congr_list (fun s hs => hbitq s (List.mem_of_mem_filter hs))
theorem nodup_activeBits_ownDirectCol (E : RAMEnv) (i c k m ell nmax base : ℕ)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hperm : E.perm k c < 2 ^ E.W)
    (hbit : ∀ s, s < ell → base + (E.perm k c % m * ell + s) < 2 ^ E.W) :
    (activeBits (upPairs E i c 1
      ((List.range ell).map (fun s => upColIt k m ell nmax base s)))).Nodup := by
  rw [activeBits_ownDirectCol E i c k m ell nmax base hW hm hmM hc hbase hperm hbit]
  refine nodup_map_of_inj ?_ (List.Nodup.filter _ List.nodup_range)
  intro s hs s' hs' he
  rw [List.mem_filter, List.mem_range] at hs hs'
  omega
theorem nodup_ownDirect (CR : CRFamily) (E : RAMEnv) (i c k m ell nmax κ N t base toff Bc : ℕ)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hbase2 : base + m * ell < 2 ^ E.W) (hperm : E.perm k c < 2 ^ E.W)
    (hperm0 : E.perm 0 c < 2 ^ E.W)
    (hbit : ∀ s, s < ell → base + (E.perm k c % m * ell + s) < 2 ^ E.W)
    (htb : (Bc + 1) * c + (κ + toff) < 2 ^ E.W)
    (hjB : (Bc + 1) * c + (κ + toff) + Bc < 2 ^ E.W)
    (hjbB : (Bc + 1) * c + (κ + toff) + Bc + 1 < 2 ^ E.W)
    (helemB : ∀ j, j < Bc →
      base + m * ell + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (hcard : E.det ((Bc + 1) * c + (κ + toff)) % 2 ^ E.W = (CR.col N t c).card)
    (hcardB : (CR.col N t c).card ≤ Bc)
    (hinj : ∀ j j', j < (CR.col N t c).card → j' < (CR.col N t c).card →
      E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W
        = E.det ((Bc + 1) * c + (κ + toff) + j' + 1) % 2 ^ E.W → j = j') :
    (activeBits (upPairs E i c 1
      ((List.range ell).map (fun s => upColIt k m ell nmax base s) ++
        (List.range Bc).map (fun j => upCrIt (κ + toff) (Bc + 1) (base + m * ell) j)))).Nodup := by
  rw [upPairs_append, activeBits_append]
  refine nodup_append_list
    (nodup_activeBits_ownDirectCol E i c k m ell nmax base hW hm hmM hc hbase hperm hbit)
    (nodup_activeBits_ownCr CR E i c κ N t (base + m * ell) toff Bc hW hc hperm0 hbase2 htb hjB hjbB
      helemB hcard hcardB hinj) ?_
  intro a ha b hb
  rw [activeBits_ownDirectCol E i c k m ell nmax base hW hm hmM hc hbase hperm hbit] at ha
  rw [activeBits_ownCr CR E i c κ N t (base + m * ell) toff Bc hW hc hperm0 hbase2 htb hjB hjbB
    helemB hcard hcardB] at hb
  rw [List.mem_map] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  have hs' : s < ell := List.mem_range.mp (List.mem_of_mem_filter hs)
  have hj0 : E.perm k c % m < m := Nat.mod_lt _ hm
  exact upColBits_ne_crBit hj0 hs' _
theorem upvBit_f_irrel (E : RAMEnv) (i : ℕ) (it : UpIt) (m : ℕ → ℕ) (c f f' : ℕ) :
    upvBit E i it (⟨m, c, f⟩ : UpAbs) = upvBit E i it (⟨m, c, f'⟩ : UpAbs) := rfl
theorem upvWt_f_irrel (E : RAMEnv) (i : ℕ) (it : UpIt) (m : ℕ → ℕ) (c f f' : ℕ) :
    upvWt E i it (⟨m, c, f⟩ : UpAbs) = upvWt E i it (⟨m, c, f'⟩ : UpAbs) := rfl
theorem upPairs_mul (E : RAMEnv) (i c f : ℕ) (L : List UpIt) :
    upPairs E i c f L = (upPairs E i c 1 L).map (fun q => (q.1, q.2 * f)) := by
  unfold upPairs
  rw [List.map_map]
  refine map_congr_list (fun it _ => ?_)
  have hb : upvBit E i it (⟨fun _ => 0, c, f⟩ : UpAbs)
      = upvBit E i it (⟨fun _ => 0, c, 1⟩ : UpAbs) := upvBit_f_irrel E i it (fun _ => 0) c f 1
  have hw : upvWt E i it (⟨fun _ => 0, c, f⟩ : UpAbs)
      = upvWt E i it (⟨fun _ => 0, c, 1⟩ : UpAbs) := upvWt_f_irrel E i it (fun _ => 0) c f 1
  simp only [Function.comp_apply, hb, hw, Nat.mul_one]
  refine Prod.ext rfl ?_
  ring
theorem activeBits_map_mul_zero (L : List (ℕ × ℕ)) :
    activeBits (L.map (fun q => (q.1, q.2 * 0))) = [] := by
  induction L with
  | nil => rfl
  | cons q rest ih =>
      rw [List.map_cons, Nat.mul_zero, activeBits_cons_zero, ih]
theorem activeBits_map_mul_one (L : List (ℕ × ℕ)) :
    activeBits (L.map (fun q => (q.1, q.2 * 1))) = activeBits L := by
  have h : (fun q : ℕ × ℕ => (q.1, q.2 * 1)) = id := by
    funext q
    obtain ⟨a, b⟩ := q
    simp
  rw [h, List.map_id]
theorem activeBits_upPairs_mul (E : RAMEnv) (i c f : ℕ) (L : List UpIt) (hf : f = 0 ∨ f = 1) :
    activeBits (upPairs E i c f L)
      = if f = 1 then activeBits (upPairs E i c 1 L) else [] := by
  rw [upPairs_mul]
  rcases hf with rfl | rfl
  · rw [if_neg (by norm_num), activeBits_map_mul_zero]
  · rw [if_pos rfl, activeBits_map_mul_one]
theorem activeBits_ownCr_gated (CR : CRFamily) (E : RAMEnv) (i c κ N t base toff Bc f : ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hperm : E.perm 0 c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (htb : (Bc + 1) * c + (κ + toff) < 2 ^ E.W)
    (hjB : (Bc + 1) * c + (κ + toff) + Bc < 2 ^ E.W)
    (hjbB : (Bc + 1) * c + (κ + toff) + Bc + 1 < 2 ^ E.W)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (hcard : E.det ((Bc + 1) * c + (κ + toff)) % 2 ^ E.W = (CR.col N t c).card)
    (hcardB : (CR.col N t c).card ≤ Bc) (hf : f = 0 ∨ f = 1) :
    activeBits (upPairs E i c f ((List.range Bc).map (fun j => upCrIt (κ + toff) (Bc + 1) base j)))
      = if f = 1 then (List.range (CR.col N t c).card).map
          (fun j => base + E.det ((Bc + 1) * c + (κ + toff) + j + 1) % 2 ^ E.W) else [] := by
  rw [activeBits_upPairs_mul E i c f _ hf,
    activeBits_ownCr CR E i c κ N t base toff Bc hW hc hperm hbase htb hjB hjbB helemB hcard hcardB]
theorem bitVal_direct_left {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (r : Node.Seed (.direct sch t)) (x : Finset ℕ) (q : Fin (sch.m * sch.ℓ)) :
    bitVal CR (.direct sch t) r (Fin.castAdd (CR.rows sch.N t) q) x
      = sch.code (finProdFinEquiv.symm q).1 (r.2 (finProdFinEquiv.symm q).1)
          (sch.rowOf r x (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 := by
  simp only [bitVal, Fin.append_left]
theorem bitVal_direct_right {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (r : Node.Seed (.direct sch t)) (x : Finset ℕ) (q : Fin (CR.rows sch.N t)) :
    bitVal CR (.direct sch t) r (Fin.natAdd (sch.m * sch.ℓ) q) x
      = if (q.val : ℕ) ∈ CR.sketch sch.N t x then 1 else 0 := by
  simp only [bitVal, Fin.append_right]
theorem bitBlock_cr {CR : CRFamily} (N t c base : ℕ) (r : Node.Seed (.cr N t))
    (hcolrange : CR.col N t c ⊆ Finset.range (CR.rows N t)) :
    bitBlock CR (.cr N t) r {c} base = (CR.col N t c).image (fun a => base + a) := by
  ext a
  rw [mem_bitBlock]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hsk : (p.val : ℕ) ∈ CR.sketch N t ({c} : Finset ℕ) := by
      by_contra hc
      rw [show bitVal CR (.cr N t) r p ({c} : Finset ℕ) = 0 from by
        simp only [bitVal]; rw [if_neg hc]] at hp
      exact zero_ne_one hp
    rw [cr_sketch_singleton] at hsk
    exact Finset.mem_image.mpr ⟨p.val, (Finset.mem_filter.mp hsk).2, rfl⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    have hvN : v < CR.rows N t := Finset.mem_range.mp (hcolrange hv)
    refine ⟨⟨v, hvN⟩, ?_, rfl⟩
    have hsk : v ∈ CR.sketch N t ({c} : Finset ℕ) := by
      rw [cr_sketch_singleton]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvN, hv⟩
    simp only [bitVal]
    rw [if_pos hsk]
theorem bitBlock_direct {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (r : Node.Seed (.direct sch t)) (x : Finset ℕ) (base : ℕ) :
    bitBlock CR (.direct sch t) r x base
      = ((Finset.univ.filter (fun q : Fin (sch.m * sch.ℓ) =>
            sch.code (finProdFinEquiv.symm q).1 (r.2 (finProdFinEquiv.symm q).1)
              (sch.rowOf r x (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2 = 1)).image
            (fun q => base + q.val))
        ∪ ((Finset.univ.filter (fun q : Fin (CR.rows sch.N t) =>
              (q.val : ℕ) ∈ CR.sketch sch.N t x)).image
            (fun q => base + (sch.m * sch.ℓ + q.val))) := by
  ext a
  rw [mem_bitBlock]
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases hlt : p.val < sch.m * sch.ℓ
    · have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hlt⟩ := Fin.ext rfl
      rw [hp', bitVal_direct_left] at hp
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨⟨p.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩))
    · have hlt2 : p.val - sch.m * sch.ℓ < CR.rows sch.N t := by
        have := p.isLt
        simp only [synLen] at this
        omega
      have hp' : p = Fin.natAdd (sch.m * sch.ℓ) ⟨p.val - sch.m * sch.ℓ, hlt2⟩ := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [hp', bitVal_direct_right] at hp
      have hmem : ((⟨p.val - sch.m * sch.ℓ, hlt2⟩ : Fin (CR.rows sch.N t)).val : ℕ)
          ∈ CR.sketch sch.N t x := by
        by_cases hc : ((⟨p.val - sch.m * sch.ℓ, hlt2⟩ : Fin (CR.rows sch.N t)).val : ℕ)
            ∈ CR.sketch sch.N t x
        · exact hc
        · rw [if_neg hc] at hp
          exact absurd hp zero_ne_one
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨⟨p.val - sch.m * sch.ℓ, hlt2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩))
      show base + (sch.m * sch.ℓ + (p.val - sch.m * sch.ℓ)) = base + p.val
      omega
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      exact ⟨Fin.castAdd (CR.rows sch.N t) q,
        by rw [bitVal_direct_left]; exact (Finset.mem_filter.mp hq).2, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      refine ⟨Fin.natAdd (sch.m * sch.ℓ) q, ?_, ?_⟩
      · rw [bitVal_direct_right, if_pos (Finset.mem_filter.mp hq).2]
      · simp only [Fin.val_natAdd]
theorem toFinset_map {α β : Type} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext b
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, rfl⟩
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩)
theorem toFinset_nil' : ([] : List ℕ).toFinset = ∅ := rfl
theorem image_comp {α β γ : Type} [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (s : Finset α) :
    s.image (fun a => g (f a)) = (s.image f).image g := by
  ext c
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
theorem activeBits_ownCr_bitBlock {CR : CRFamily} (E : RAMEnv) (i N t c base toff Bc f : ℕ)
    (r : Node.Seed (.cr N t)) (k : ℕ) (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hperm : E.perm 0 c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (hdet : E.det = upDet cnt W colBase items tab)
    (hAt : UpTabAt CR Bc tab toff N t)
    (hcolrange : CR.col N t c ⊆ Finset.range (CR.rows N t))
    (hrows : CR.rows N t ≤ 2 ^ E.W)
    (hBcW : Bc < 2 ^ E.W) (hcolBase : 4 < colBase) (hcN : c < N)
    (hbig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W)
    (hcardB : (CR.col N t c).card ≤ Bc)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (hf : f = 0 ∨ f = 1) :
    (activeBits (upPairs E i c f (upOwnItems CR Bc colBase (.cr N t) k base toff))).toFinset
      = if f = 1 then bitBlock CR (.cr N t) r ({c} : Finset ℕ) base else ∅ := by
  have hown : upOwnItems CR Bc colBase (.cr N t) k base toff
      = (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) base j) := by
    simp only [upOwnItems]
  have hcard : E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W = (CR.col N t c).card := by
    rw [hdet]
    rw [upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
    have hsub : (Bc + 1) * c + (colBase + toff) - colBase = toff + (Bc + 1) * c := by omega
    rw [hsub, (hAt c hcN).1]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hown, activeBits_ownCr_gated CR E i c colBase N t base toff Bc f hW hc hperm hbase
    (by omega) (by omega) (by omega) helemB hcard hcardB hf]
  by_cases hf1 : f = 1
  · rw [if_pos hf1, if_pos hf1, bitBlock_cr N t c base r hcolrange,
      toFinset_map, List.toFinset_range]
    have hg : ∀ j, j < (CR.col N t c).card →
        base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
          = base + tab (toff + (Bc + 1) * c + 1 + j) := by
      intro j hj
      have hlt : tab (toff + (Bc + 1) * c + 1 + j) < 2 ^ E.W := by
        have hmem : tab (toff + (Bc + 1) * c + 1 + j) ∈ CR.col N t c := by
          have himg := (hAt c hcN).2
          rw [← himg]
          exact Finset.mem_image.mpr
            ⟨j, Finset.mem_range.mpr (by rw [(hAt c hcN).1]; exact hj), rfl⟩
        have h2 := hcolrange hmem
        rw [Finset.mem_range] at h2
        omega
      rw [hdet, upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
      have hsub : (Bc + 1) * c + (colBase + toff) + j + 1 - colBase
          = toff + (Bc + 1) * c + 1 + j := by omega
      rw [hsub, Nat.mod_eq_of_lt hlt]
    have step1 : (Finset.range (CR.col N t c).card).image
        (fun j => base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W)
        = (Finset.range (CR.col N t c).card).image
          (fun j => base + tab (toff + (Bc + 1) * c + 1 + j)) := by
      ext a
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, (hg j hj).symm⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, hg j hj⟩
    have step2 : (Finset.range (CR.col N t c).card).image
          (fun j => base + tab (toff + (Bc + 1) * c + 1 + j))
        = (CR.col N t c).image (fun a => base + a) := by
      have himg : (Finset.range (CR.col N t c).card).image
            (fun j => tab (toff + (Bc + 1) * c + 1 + j)) = CR.col N t c := by
        rw [← (hAt c hcN).1]
        exact (hAt c hcN).2
      rw [image_comp, himg]
    rw [step1, step2]
  · rw [if_neg hf1, if_neg hf1, toFinset_nil']
theorem toFinset_range_filter (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range n).filter p).toFinset = (Finset.range n).filter p := by
  ext a
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter,
    Finset.mem_range, decide_eq_true_eq]
theorem range_filter_eq_image_univ (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.range n).filter p
      = ((Finset.univ : Finset (Fin n)).filter (fun s => p s.val)).image Fin.val := by
  ext a
  constructor
  · intro ha
    obtain ⟨hlt, hp⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_image.mpr
      ⟨⟨a, Finset.mem_range.mp hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  · intro ha
    obtain ⟨s, hs, hsa⟩ := Finset.mem_image.mp ha
    obtain ⟨-, hp⟩ := Finset.mem_filter.mp hs
    rw [← hsa]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr s.isLt, hp⟩
def rowOf0 (sch : RowScheme) (π : Equiv.Perm (Fin sch.N)) {c : ℕ} (hc : c < sch.N)
    (hm : 0 < sch.m) : Fin sch.m :=
  ⟨(π ⟨c, hc⟩).val % sch.m, Nat.mod_lt _ hm⟩
theorem rowOf_singleton_rowOf0 {sch : RowScheme} {c : ℕ} (lr : sch.LocalSeed) (hcN : c < sch.N)
    (hm : 0 < sch.m) (j : Fin sch.m) :
    sch.rowOf lr ({c} : Finset ℕ) j
      = if j = rowOf0 sch lr.1 hcN hm then {(lr.1 ⟨c, hcN⟩).val / sch.m} else ∅ := by
  rw [RowScheme.rowOf, rowImage_singleton lr.1 hcN j.val]
  by_cases h : (lr.1 ⟨c, hcN⟩).val % sch.m = j.val
  · rw [if_pos h, if_pos (Fin.ext h.symm)]
  · rw [if_neg h, if_neg]
    intro hj
    exact h (by rw [hj]; rfl)
theorem div_lt_schemeNmax (sch : RowScheme) (hm : 0 < sch.m) {c : ℕ} (hc : c < sch.N) :
    c / sch.m < schemeNmax sch := by
  rw [schemeNmax, Nat.lt_ceil]
  have hmR : (0 : ℝ) < (sch.m : ℝ) := by exact_mod_cast hm
  have hcR : (c : ℝ) < (sch.N : ℝ) := by exact_mod_cast hc
  calc ((c / sch.m : ℕ) : ℝ) ≤ (c : ℝ) / (sch.m : ℝ) := Nat.cast_div_le
    _ < (sch.N : ℝ) / (sch.m : ℝ) := by
        rw [div_lt_div_iff_of_pos_right hmR]
        exact hcR
theorem upvImg_colIt (E : RAMEnv) (i k m ell nmax base s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hperm : E.perm k ab.c < 2 ^ E.W) :
    upvImg E i (upColIt k m ell nmax base s) ab = E.perm k ab.c := by
  have hfrom0 : (upColIt k m ell nmax base s).fromI = 0 := rfl
  have hsrc0 : (upColIt k m ell nmax base s).srcC = 0 := rfl
  have hZ1 : upvZ1 E (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ1, upColIt]
  have hZ2 : upvZ2 E i (upColIt k m ell nmax base s) = 0 := by
    simp only [upvZ2, hfrom0, Nat.zero_mul, Nat.zero_mod]
  have hZ3 : upvZ3 E (upColIt k m ell nmax base s) = 1 := by
    simp only [upvZ3, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ4 : upvZ4 E (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ4, hZ1, hZ3, Nat.mul_one, Nat.mod_mod]
  have hZ5 : upvZ5 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ5, hZ4, hZ2, Nat.add_zero, Nat.mod_mod]
  have hZ6 : upvZ6 E (upColIt k m ell nmax base s) ab = 0 := by
    simp only [upvZ6, hsrc0, Nat.zero_mul, Nat.zero_mod]
  have hZ7 : upvZ7 E (upColIt k m ell nmax base s) = 1 := by
    simp only [upvZ7, hsrc0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ8 : upvZ8 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_one, Nat.mod_mod]
  simp only [upvImg, hZ8, hZ6, Nat.add_zero, Nat.mod_eq_of_lt hperm]
theorem upvJ0_colIt (E : RAMEnv) (i k m ell nmax base s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hperm : E.perm k ab.c < 2 ^ E.W) :
    upvJ0 E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % m := by
  rw [upvJ0, upvImg_colIt E i k m ell nmax base s ab hW hperm]
  simp only [upColIt]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hm) hmM)
theorem upvPos_colIt (E : RAMEnv) (i k m ell nmax base s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hperm : E.perm k ab.c < 2 ^ E.W) :
    upvPos E i (upColIt k m ell nmax base s) ab = E.perm k ab.c / m := by
  rw [upvPos, upvImg_colIt E i k m ell nmax base s ab hW hperm]
  simp only [upColIt]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hperm)
theorem upvCoin_colIt (E : RAMEnv) (i k m ell nmax base s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hperm : E.perm k ab.c < 2 ^ E.W)
    (hbit : E.perm k ab.c % m * ell + s < 2 ^ E.W)
    (hqn : (E.perm k ab.c % m * ell + s) * nmax < 2 ^ E.W)
    (hqnp : (E.perm k ab.c % m * ell + s) * nmax + E.perm k ab.c / m < 2 ^ E.W) :
    upvCoin E i (upColIt k m ell nmax base s) ab
      = E.coeff k ((E.perm k ab.c % m * ell + s) * nmax + E.perm k ab.c / m) % 2 ^ E.W := by
  have hJ0 := upvJ0_colIt E i k m ell nmax base s ab hW hm hmM hperm
  have hPos := upvPos_colIt E i k m ell nmax base s ab hW hperm
  have hY3 : upvY3 E i (upColIt k m ell nmax base s) ab = (E.perm k ab.c % m) * ell := by
    rw [upvY3, hJ0]
    simp only [upColIt]
    exact Nat.mod_eq_of_lt (by omega)
  have hQ : upvQ E i (upColIt k m ell nmax base s) ab = E.perm k ab.c % m * ell + s := by
    rw [upvQ, hY3]
    simp only [upColIt]
    exact Nat.mod_eq_of_lt hbit
  have hY4 : upvY4 E i (upColIt k m ell nmax base s) ab
      = (E.perm k ab.c % m * ell + s) * nmax := by
    rw [upvY4, hQ]
    simp only [upColIt]
    exact Nat.mod_eq_of_lt hqn
  unfold upvCoin
  rw [upvY5, hY4, hPos, Nat.mod_eq_of_lt hqnp]
  simp only [upColIt]
theorem upvWt_colIt_eq (E : RAMEnv) (i k m ell nmax base c s : ℕ)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hperm : E.perm k c < 2 ^ E.W)
    (hbit : base + (E.perm k c % m * ell + s) < 2 ^ E.W)
    (hqn : (E.perm k c % m * ell + s) * nmax < 2 ^ E.W)
    (hqnp : (E.perm k c % m * ell + s) * nmax + E.perm k c / m < 2 ^ E.W) :
    upvWt E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
        * (upColIt k m ell nmax base s).mOn
      = E.coeff k ((E.perm k c % m * ell + s) * nmax + E.perm k c / m) % 2 ^ E.W := by
  have hbit0 : E.perm k c % m * ell + s < 2 ^ E.W := by omega
  obtain ⟨-, -, -, hWt⟩ :=
    upColIt_apply E i k m ell nmax base s (⟨fun _ => 0, c, 1⟩ : UpAbs)
      hW hm hmM hc hW hbase hperm hbit
  have hcoin := upvCoin_colIt E i k m ell nmax base s (⟨fun _ => 0, c, 1⟩ : UpAbs)
    hW hm hmM hperm hbit0 hqn hqnp
  have hcoin' : upvCoin E i (upColIt k m ell nmax base s) (⟨fun _ => 0, c, 1⟩ : UpAbs)
      = E.coeff k ((E.perm k c % m * ell + s) * nmax + E.perm k c / m) % 2 ^ E.W := hcoin
  have hmOn : (upColIt k m ell nmax base s).mOn = 1 := rfl
  rw [hWt, hmOn, Nat.mul_one, Nat.mul_one, hcoin', Nat.mod_mod]
theorem direct_col_collapse {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (lr : sch.LocalSeed) {c : ℕ} (hcN : c < sch.N) (hm : 0 < sch.m) (base : ℕ) :
    ((Finset.univ.filter (fun q : Fin (sch.m * sch.ℓ) =>
        sch.code (finProdFinEquiv.symm q).1 (lr.2 (finProdFinEquiv.symm q).1)
          (sch.rowOf lr ({c} : Finset ℕ) (finProdFinEquiv.symm q).1)
          (finProdFinEquiv.symm q).2 = 1)).image (fun q => base + q.val))
      = ((Finset.univ : Finset (Fin sch.ℓ)).filter (fun s =>
          sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1)).image
        (fun s => base + ((rowOf0 sch lr.1 hcN hm).val * sch.ℓ + s.val)) := by
  classical
  set j0 : Fin sch.m := rowOf0 sch lr.1 hcN hm with hj0
  ext a
  constructor
  · intro ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨-, hQ⟩ := Finset.mem_filter.mp hq
    have hQ' : sch.code q.divNat (lr.2 q.divNat)
        (sch.rowOf lr ({c} : Finset ℕ) q.divNat) q.modNat = 1 := hQ
    have hqval : q.val = sch.ℓ * (q.divNat : Fin sch.m).val + (q.modNat : Fin sch.ℓ).val := by
      rw [show (q.divNat : Fin sch.m).val = q.val / sch.ℓ from rfl,
        show (q.modNat : Fin sch.ℓ).val = q.val % sch.ℓ from rfl]
      exact (Nat.div_add_mod q.val sch.ℓ).symm
    by_cases hj : (q.divNat : Fin sch.m) = j0
    · have hQ'' : sch.code j0 (lr.2 j0) (sch.rowOf lr ({c} : Finset ℕ) j0) q.modNat = 1 := by
        rw [← hj]
        exact hQ'
      refine Finset.mem_image.mpr ⟨q.modNat, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ''⟩
      · show base + (j0.val * sch.ℓ + q.modNat.val) = base + q.val
        rw [hqval, hj, Nat.mul_comm sch.ℓ j0.val]
    · have hrow : sch.rowOf lr ({c} : Finset ℕ) (q.divNat : Fin sch.m) = ∅ := by
        rw [rowOf_singleton_rowOf0 (lr := lr) hcN hm (q.divNat : Fin sch.m), if_neg hj]
      rw [hrow, code_empty] at hQ'
      exact absurd hQ' (by norm_num)
  · intro ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨-, hP⟩ := Finset.mem_filter.mp hs
    have h2 : ((finProdFinEquiv (j0, s)).divNat, (finProdFinEquiv (j0, s)).modNat) = (j0, s) := by
      rw [← finProdFinEquiv_symm_apply, Equiv.symm_apply_apply]
    have hd : (finProdFinEquiv (j0, s)).divNat = j0 := congrArg Prod.fst h2
    have hm2 : (finProdFinEquiv (j0, s)).modNat = s := congrArg Prod.snd h2
    refine Finset.mem_image.mpr ⟨finProdFinEquiv (j0, s), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [finProdFinEquiv_symm_apply, hd, hm2]
      exact hP
    · show base + (s.val + sch.ℓ * j0.val) = base + (j0.val * sch.ℓ + s.val)
      rw [Nat.mul_comm sch.ℓ j0.val, Nat.add_comm s.val (j0.val * sch.ℓ)]
theorem direct_residual {CR : CRFamily} {sch : RowScheme} {t c : ℕ}
    (hcolrange : CR.col sch.N t c ⊆ Finset.range (CR.rows sch.N t)) (base : ℕ) :
    ((Finset.univ.filter (fun q : Fin (CR.rows sch.N t) =>
        (q.val : ℕ) ∈ CR.sketch sch.N t ({c} : Finset ℕ))).image
        (fun q => base + (sch.m * sch.ℓ + q.val)))
      = (CR.col sch.N t c).image (fun a => base + sch.m * sch.ℓ + a) := by
  ext a
  constructor
  · intro ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hsk : (q.val : ℕ) ∈ CR.sketch sch.N t ({c} : Finset ℕ) := (Finset.mem_filter.mp hq).2
    rw [cr_sketch_singleton] at hsk
    exact Finset.mem_image.mpr ⟨q.val, (Finset.mem_filter.mp hsk).2, Nat.add_assoc _ _ _⟩
  · intro ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    have hvN : v < CR.rows sch.N t := Finset.mem_range.mp (hcolrange hv)
    refine Finset.mem_image.mpr ⟨⟨v, hvN⟩, ?_, (Nat.add_assoc _ _ _).symm⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [cr_sketch_singleton]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvN, hv⟩
theorem activeBits_ownDirectCol_bitBlock {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (E : RAMEnv) (i c k base : ℕ) (lr : sch.LocalSeed)
    (hW : 1 < 2 ^ E.W) (hm : 0 < sch.m) (hmM : sch.m ≤ 2 ^ E.W) (hcW : c < 2 ^ E.W)
    (hcN : c < sch.N) (hbase : base < 2 ^ E.W) (hperm : E.perm k c < 2 ^ E.W)
    (hπε : E.perm k c = (lr.1 ⟨c, hcN⟩).val)
    (hbit : ∀ s, s < sch.ℓ → base + (E.perm k c % sch.m * sch.ℓ + s) < 2 ^ E.W)
    (hqnp : ∀ s : Fin sch.ℓ,
      (E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m < 2 ^ E.W)
    (hcoef : ∀ s : Fin sch.ℓ,
      E.coeff k ((E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m)
        = (sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s).val) :
    (activeBits (upPairs E i c 1 ((List.range sch.ℓ).map
        (fun s => upColIt k sch.m sch.ℓ (schemeNmax sch) base s)))).toFinset
      = ((Finset.univ : Finset (Fin sch.ℓ)).filter (fun s =>
          sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1)).image
        (fun s => base + (E.perm k c % sch.m * sch.ℓ + s.val)) := by
  classical
  have hwtpred : ∀ s : Fin sch.ℓ,
      (upvWt E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s.val)
        (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
        * (upColIt k sch.m sch.ℓ (schemeNmax sch) base s.val).mOn = 1)
      ↔ sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
          (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1 := by
    intro s
    have hs : s.val < sch.ℓ := s.isLt
    have hqn : (E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch < 2 ^ E.W :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (hqnp s)
    have hwt := upvWt_colIt_eq E i k sch.m sch.ℓ (schemeNmax sch) base c s.val
      hW hm hmM hcW hbase hperm (hbit s.val hs) hqn (hqnp s)
    have hcv : (sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
        (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s).val < 2 ^ E.W := by
      have h1 := zmod2_val_le_one (sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
        (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s)
      omega
    rw [hwt, hcoef s, Nat.mod_eq_of_lt hcv, zmod2_val_eq_ite]
    by_cases h : sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
        (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd hh h⟩
  rw [activeBits_ownDirectCol E i c k sch.m sch.ℓ (schemeNmax sch) base hW hm hmM hcW hbase hperm
    hbit]
  rw [toFinset_map, toFinset_range_filter, range_filter_eq_image_univ, ← image_comp]
  have hfil : (Finset.univ.filter (fun s : Fin sch.ℓ =>
        upvWt E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s.val)
          (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
          * (upColIt k sch.m sch.ℓ (schemeNmax sch) base s.val).mOn = 1))
      = (Finset.univ.filter (fun s : Fin sch.ℓ =>
          sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hwtpred s
  rw [hfil, hπε]
theorem activeBits_ownDirect_bitBlock {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    (E : RAMEnv) (i c k base toff Bc colBase cnt W : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (lr : sch.LocalSeed)
    (hW : 1 < 2 ^ E.W) (hm : 0 < sch.m) (hmM : sch.m ≤ 2 ^ E.W) (hcW : c < 2 ^ E.W)
    (hcN : c < sch.N) (hbase : base < 2 ^ E.W) (hbase2 : base + sch.m * sch.ℓ < 2 ^ E.W)
    (hperm : E.perm k c < 2 ^ E.W) (hperm0 : E.perm 0 c < 2 ^ E.W)
    (hπε : E.perm k c = (lr.1 ⟨c, hcN⟩).val)
    (hbit : ∀ s, s < sch.ℓ → base + (E.perm k c % sch.m * sch.ℓ + s) < 2 ^ E.W)
    (hqnp : ∀ s : Fin sch.ℓ,
      (E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m < 2 ^ E.W)
    (hcoef : ∀ s : Fin sch.ℓ,
      E.coeff k ((E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m)
        = (sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s).val)
    (hdet : E.det = upDet cnt W colBase items tab)
    (hAt : UpTabAt CR Bc tab toff sch.N t)
    (hcolrange : CR.col sch.N t c ⊆ Finset.range (CR.rows sch.N t))
    (hrows : CR.rows sch.N t ≤ 2 ^ E.W)
    (hBcW : Bc < 2 ^ E.W) (hcolBase : 4 < colBase)
    (hbig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W)
    (hcardB : (CR.col sch.N t c).card ≤ Bc)
    (helemB : ∀ j, j < Bc →
      base + sch.m * sch.ℓ + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
        < 2 ^ E.W) :
    (activeBits (upPairs E i c 1 (upOwnItems CR Bc colBase (.direct sch t) k base toff))).toFinset
      = bitBlock CR (.direct sch t) lr ({c} : Finset ℕ) base := by
  have hown : upOwnItems CR Bc colBase (.direct sch t) k base toff
      = (List.range sch.ℓ).map (fun s => upColIt k sch.m sch.ℓ (schemeNmax sch) base s) ++
        (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j) := by
    simp only [upOwnItems]
  have hcard : E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W = (CR.col sch.N t c).card := by
    rw [hdet, upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
    have hsub : (Bc + 1) * c + (colBase + toff) - colBase = toff + (Bc + 1) * c := by omega
    rw [hsub, (hAt c hcN).1]
    exact Nat.mod_eq_of_lt (by omega)
  have hcolpart := activeBits_ownDirectCol_bitBlock (CR := CR) (sch := sch) (t := t) E i c k base lr
    hW hm hmM hcW hcN hbase hperm hπε hbit hqnp hcoef
  have hcr : activeBits (upPairs E i c 1 ((List.range Bc).map
      (fun j => upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j)))
      = (List.range (CR.col sch.N t c).card).map
        (fun j => base + sch.m * sch.ℓ + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W) :=
    activeBits_ownCr CR E i c colBase sch.N t (base + sch.m * sch.ℓ) toff Bc hW hcW hperm0 hbase2
      (by omega) (by omega) (by omega) helemB hcard hcardB
  have hrespart : ((List.range (CR.col sch.N t c).card).map
      (fun j => base + sch.m * sch.ℓ + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W)).toFinset
      = (CR.col sch.N t c).image (fun a => base + sch.m * sch.ℓ + a) := by
    have hunf : upOwnItems CR Bc colBase (.cr sch.N t) k (base + sch.m * sch.ℓ) toff
        = (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j) := by
      simp only [upOwnItems]
    have hrec := activeBits_ownCr_bitBlock (CR := CR) (E := E) (i := i) (N := sch.N) (t := t)
      (c := c) (base := base + sch.m * sch.ℓ) (toff := toff) (Bc := Bc) (f := 1) (r := ())
      (k := k) (cnt := cnt) (W := W) (colBase := colBase) (items := items) (tab := tab)
      hW hcW hperm0 hbase2 hdet hAt hcolrange hrows hBcW hcolBase hcN hbig hcardB helemB (Or.inr rfl)
    rw [if_pos rfl] at hrec
    have hbc := bitBlock_cr (CR := CR) (N := sch.N) (t := t) (c := c)
      (base := base + sch.m * sch.ℓ) (r := ()) hcolrange
    rw [← hcr, ← hunf, hrec, hbc]
  have hcolset : ((Finset.univ : Finset (Fin sch.ℓ)).filter (fun s =>
        sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
          (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1)).image
        (fun s => base + (E.perm k c % sch.m * sch.ℓ + s.val))
      = ((Finset.univ : Finset (Fin sch.ℓ)).filter (fun s =>
          sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s = 1)).image
        (fun s => base + ((rowOf0 sch lr.1 hcN hm).val * sch.ℓ + s.val)) := by
    simp only [hπε, rowOf0]
  have hbb := @bitBlock_direct CR sch t lr ({c} : Finset ℕ) base
  rw [hown, upPairs_append, activeBits_append, List.toFinset_append, hcolpart, hcr, hrespart, hbb,
    direct_residual (CR := CR) (sch := sch) (t := t) (c := c) hcolrange base,
    direct_col_collapse (CR := CR) (sch := sch) (t := t) lr hcN hm base, hcolset]
def PermAl (E : RAMEnv) (k N : ℕ) (π : Equiv.Perm (Fin N)) : Prop :=
  ∀ (a : ℕ) (ha : a < N), E.perm k a = (π ⟨a, ha⟩).val
def CoefAl (P : HintParams) (E : RAMEnv) (k N X Y : ℕ) (β : NodeCoins P N X Y) : Prop :=
  ∀ (j : Fin (P.rows X Y)) (s : Fin (P.ell N X Y)) (v : Fin (P.Nmax N X Y)),
    E.coeff k ((j.val * P.ell N X Y + s.val) * P.Nmax N X Y + v.val) = ((β j s v : ZMod 2)).val
universe u
theorem det_eq_tab {E : RAMEnv} {cnt W colBase : ℕ} {items : List UpIt} {tab : ℕ → ℕ}
    {Bc toff c j : ℕ}
    (hdet : E.det = upDet cnt W colBase items tab) (hcolBase : 4 < colBase) :
    E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
      = tab (toff + (Bc + 1) * c + 1 + j) % 2 ^ E.W := by
  rw [hdet, upDet_tab cnt W colBase items tab ((Bc + 1) * c + (colBase + toff) + j + 1)
    (by omega) (by omega)]
  have harg : (Bc + 1) * c + (colBase + toff) + j + 1 - colBase
      = toff + (Bc + 1) * c + 1 + j := by omega
  rw [harg]
theorem upCrIt_point (CR : CRFamily) (E : RAMEnv) (i N t c f : ℕ) (base toff Bc colBase cnt W : ℕ)
    (items : List UpIt) (tab : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) (hf01 : f = 0 ∨ f = 1)
    (hperm0 : E.perm 0 c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (hdet : E.det = upDet cnt W colBase items tab)
    (hAt : UpTabAt CR Bc tab toff N t) (hcN : c < N)
    (hbig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W) (hcolBase : 4 < colBase)
    (hcardB : (CR.col N t c).card ≤ Bc)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W) :
    ∀ j, j < Bc →
      upvBit E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs)
          = base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W ∧
        upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs) * f
          < 2 := by
  intro j hj
  have hcard : E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W = (CR.col N t c).card := by
    rw [hdet, upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
    have hsub : (Bc + 1) * c + (colBase + toff) - colBase = toff + (Bc + 1) * c := by omega
    rw [hsub, (hAt c hcN).1]
    exact Nat.mod_eq_of_lt (by omega)
  have htb : (Bc + 1) * c + (colBase + toff) < 2 ^ E.W := by omega
  have hjc : (Bc + 1) * c + (colBase + toff) + j < 2 ^ E.W := by omega
  have hjb : (Bc + 1) * c + (colBase + toff) + j + 1 < 2 ^ E.W := by omega
  have helem : E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W + base < 2 ^ E.W := by
    have := helemB j hj
    omega
  obtain ⟨-, -, hBit, hWt, hVal⟩ :=
    upCrIt_apply E i (colBase + toff) (Bc + 1) base j (⟨fun _ => 0, c, f⟩ : UpAbs)
      hW hc hf hbase htb hjc hjb helem hperm0
  have hVal' : upvValid E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs)
      = if j < E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W then 1 else 0 := hVal
  have hBit' : upvBit E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs)
      = base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W := hBit
  refine ⟨hBit', ?_⟩
  rw [hWt, hVal', hcard]
  by_cases hjc' : j < (CR.col N t c).card
  · rw [if_pos hjc', Nat.one_mul]
    rcases hf01 with h | h <;> rw [h] <;> norm_num
  · rw [if_neg hjc', Nat.zero_mul]
    norm_num
theorem upFold_node_direct (CR : CRFamily) (E : RAMEnv) (i base c f a : ℕ)
    {sch : RowScheme} {t : ℕ} (lr : sch.LocalSeed) (k toff Bc colBase sav : ℕ)
    (cnt W : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) (hf01 : f = 0 ∨ f = 1)
    (hperm : ∀ k a, E.perm k a < 2 ^ E.W)
    (hm : 0 < sch.m) (hmM : sch.m ≤ 2 ^ E.W)
    (hcN : c < sch.N) (hbase : base < 2 ^ E.W) (hbase2 : base + sch.m * sch.ℓ < 2 ^ E.W)
    (hπε : E.perm k c = (lr.1 ⟨c, hcN⟩).val)
    (hbit : ∀ s, s < sch.ℓ → base + (E.perm k c % sch.m * sch.ℓ + s) < 2 ^ E.W)
    (hqnp : ∀ s : Fin sch.ℓ,
      (E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m < 2 ^ E.W)
    (hcoef : ∀ s : Fin sch.ℓ,
      E.coeff k ((E.perm k c % sch.m * sch.ℓ + s.val) * schemeNmax sch + E.perm k c / sch.m)
        = (sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) s).val)
    (hdet : E.det = upDet cnt W colBase items tab)
    (hAt : UpTabAt CR Bc tab toff sch.N t)
    (hcolrange : CR.col sch.N t c ⊆ Finset.range (CR.rows sch.N t))
    (hrows : CR.rows sch.N t ≤ 2 ^ E.W) (hBcW : Bc < 2 ^ E.W) (hcolBase : 4 < colBase)
    (hbig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W)
    (hcardB : (CR.col sch.N t c).card ≤ Bc)
    (helemB : ∀ j, j < Bc →
      base + sch.m * sch.ℓ + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
        < 2 ^ E.W)
    (mem : ℕ → ℕ) (hmem : ∀ x, mem x < 2 ^ E.W) :
    (upFold E i ⟨mem, c, f⟩
        (upOwnItems CR Bc colBase (.direct sch t) k base toff
          ++ upKids CR Bc colBase (.direct sch t) k base toff sav [])).mem a
      = mem a ^^^ packSel E.W
          (if f = 1 then bitBlock CR (.direct sch t) lr {c} base else ∅) a := by
  have hown : upOwnItems CR Bc colBase (.direct sch t) k base toff
      = (List.range sch.ℓ).map (fun s => upColIt k sch.m sch.ℓ (schemeNmax sch) base s) ++
        (List.range Bc).map (fun j =>
          upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j) := rfl
  have hkid : upKids CR Bc colBase (.direct sch t) k base toff sav ([] : List UpIt) = [] := rfl
  rw [hkid, List.append_nil]
  have hcr := upCrIt_point CR E i sch.N t c f (base + sch.m * sch.ℓ) toff Bc colBase cnt W
    items tab hW hc hf hf01 (hperm 0 c) hbase2 hdet hAt hcN hbig hcolBase hcardB helemB
  have hcolBit : ∀ s, s < sch.ℓ →
      upvBit E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s) (⟨fun _ => 0, c, f⟩ : UpAbs)
        = base + (E.perm k c % sch.m * sch.ℓ + s) := by
    intro s hs
    obtain ⟨-, -, hB, -⟩ :=
      upColIt_apply E i k sch.m sch.ℓ (schemeNmax sch) base s (⟨fun _ => 0, c, f⟩ : UpAbs)
        hW hm hmM hc hf hbase (hperm k c) (hbit s hs)
    exact hB
  have hcolW : ∀ s, s < sch.ℓ →
      upvWt E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s) (⟨fun _ => 0, c, f⟩ : UpAbs) * f
        < 2 := by
    intro s hs
    obtain ⟨-, -, -, hWt⟩ :=
      upColIt_apply E i k sch.m sch.ℓ (schemeNmax sch) base s (⟨fun _ => 0, c, f⟩ : UpAbs)
        hW hm hmM hc hf hbase (hperm k c) (hbit s hs)
    have hqn : (E.perm k c % sch.m * sch.ℓ + s) * schemeNmax sch < 2 ^ E.W :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (hqnp ⟨s, hs⟩)
    have hbit' : E.perm k c % sch.m * sch.ℓ + s < 2 ^ E.W := by
      have h := hbit s hs
      omega
    have hcoin := upvCoin_colIt E i k sch.m sch.ℓ (schemeNmax sch) base s
      (⟨fun _ => 0, c, f⟩ : UpAbs) hW hm hmM (hperm k c) hbit' hqn (hqnp ⟨s, hs⟩)
    have hcoin' : upvCoin E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s)
        (⟨fun _ => 0, c, f⟩ : UpAbs)
        = E.coeff k ((E.perm k c % sch.m * sch.ℓ + s) * schemeNmax sch + E.perm k c / sch.m)
            % 2 ^ E.W := hcoin
    rw [hWt, hcoin', Nat.mod_mod, hcoef ⟨s, hs⟩]
    have hle : ((sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
        (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) ⟨s, hs⟩).val : ℕ) ≤ 1 :=
      zmod2_val_le_one _
    have hlt : ((sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
        (sch.rowOf lr ({c} : Finset ℕ) (rowOf0 sch lr.1 hcN hm)) ⟨s, hs⟩).val : ℕ) < 2 ^ E.W := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    rcases hf01 with h | h
    · rw [h, Nat.mul_zero]
      omega
    · rw [h, Nat.mul_one]
      omega
  have hcolLt : ∀ s, s < sch.ℓ → E.perm k c % sch.m * sch.ℓ + s < sch.m * sch.ℓ := by
    intro s hs
    have h1 : E.perm k c % sch.m < sch.m := Nat.mod_lt _ hm
    calc E.perm k c % sch.m * sch.ℓ + s < E.perm k c % sch.m * sch.ℓ + sch.ℓ := by omega
      _ = (E.perm k c % sch.m + 1) * sch.ℓ := by rw [Nat.succ_mul]
      _ ≤ sch.m * sch.ℓ := Nat.mul_le_mul_right _ (by omega)
  have hcolMem : ∀ s, s < sch.ℓ →
      upvBit E i (upColIt k sch.m sch.ℓ (schemeNmax sch) base s) (⟨fun _ => 0, c, f⟩ : UpAbs)
        < 2 ^ E.W := by
    intro s hs
    rw [hcolBit s hs]
    exact hbit s hs
  have hfix : ∀ it ∈ upOwnItems CR Bc colBase (.direct sch t) k base toff,
      it.setSt = 0 ∧ it.mode < 2 := by
    intro it hit
    rw [hown, List.mem_append] at hit
    rcases hit with hit | hit
    · rw [List.mem_map] at hit
      obtain ⟨s, -, rfl⟩ := hit
      exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
    · rw [List.mem_map] at hit
      obtain ⟨j, -, rfl⟩ := hit
      exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
  have hbitAll : ∀ it ∈ upOwnItems CR Bc colBase (.direct sch t) k base toff, ∀ m : ℕ → ℕ,
      upvBit E i it (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_append] at hit
    rw [upvBit_mem_irrel E i it c f m (fun _ => 0)]
    rcases hit with hit | hit
    · rw [List.mem_map] at hit
      obtain ⟨s, hs, rfl⟩ := hit
      exact hcolMem s (List.mem_range.mp hs)
    · rw [List.mem_map] at hit
      obtain ⟨j, hj, rfl⟩ := hit
      rw [(hcr j (List.mem_range.mp hj)).1]
      exact helemB j (List.mem_range.mp hj)
  have hwtfAll : ∀ it ∈ upOwnItems CR Bc colBase (.direct sch t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_append] at hit
    rw [upvWt_mem_irrel E i it c f m (fun _ => 0)]
    rcases hit with hit | hit
    · rw [List.mem_map] at hit
      obtain ⟨s, hs, rfl⟩ := hit
      have := hcolW s (List.mem_range.mp hs)
      omega
    · rw [List.mem_map] at hit
      obtain ⟨j, hj, rfl⟩ := hit
      have := (hcr j (List.mem_range.mp hj)).2
      omega
  have hmulAll : ∀ it ∈ upOwnItems CR Bc colBase (.direct sch t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_append] at hit
    rw [upvWt_mem_irrel E i it c f m (fun _ => 0)]
    rcases hit with hit | hit
    · rw [List.mem_map] at hit
      obtain ⟨s, hs, rfl⟩ := hit
      have hmOn : (upColIt k sch.m sch.ℓ (schemeNmax sch) base s).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      have := hcolW s (List.mem_range.mp hs)
      omega
    · rw [List.mem_map] at hit
      obtain ⟨j, hj, rfl⟩ := hit
      have hmOn : (upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      have := (hcr j (List.mem_range.mp hj)).2
      omega
  have hmul2All : ∀ it ∈ upOwnItems CR Bc colBase (.direct sch t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 := by
    intro it hit m
    rw [hown, List.mem_append] at hit
    rw [upvWt_mem_irrel E i it c f m (fun _ => 0)]
    rcases hit with hit | hit
    · rw [List.mem_map] at hit
      obtain ⟨s, hs, rfl⟩ := hit
      have hmOn : (upColIt k sch.m sch.ℓ (schemeNmax sch) base s).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      exact hcolW s (List.mem_range.mp hs)
    · rw [List.mem_map] at hit
      obtain ⟨j, hj, rfl⟩ := hit
      have hmOn : (upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      exact (hcr j (List.mem_range.mp hj)).2
  have hwtAll : ∀ q ∈ upPairs E i c f
      (upOwnItems CR Bc colBase (.direct sch t) k base toff), q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    rw [hown, upPairs_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rw [upPairs_map, List.mem_map] at hq
      obtain ⟨s, hs, rfl⟩ := hq
      have hmOn : (upColIt k sch.m sch.ℓ (schemeNmax sch) base s).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      have := hcolW s (List.mem_range.mp hs)
      omega
    · rw [upPairs_map, List.mem_map] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have hmOn : (upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j).mOn = 1 := rfl
      rw [hmOn, Nat.mul_one]
      have := (hcr j (List.mem_range.mp hj)).2
      omega
  have hbitqAll : ∀ q ∈ upPairs E i c f
      (upOwnItems CR Bc colBase (.direct sch t) k base toff), q.1 < 2 ^ E.W := by
    intro q hq
    rw [hown, upPairs_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rw [upPairs_map, List.mem_map] at hq
      obtain ⟨s, hs, rfl⟩ := hq
      exact hcolMem s (List.mem_range.mp hs)
    · rw [upPairs_map, List.mem_map] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      rw [(hcr j (List.mem_range.mp hj)).1]
      exact helemB j (List.mem_range.mp hj)
  have hinj : ∀ j j', j < (CR.col sch.N t c).card → j' < (CR.col sch.N t c).card →
      E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
        = E.det ((Bc + 1) * c + (colBase + toff) + j' + 1) % 2 ^ E.W → j = j' := by
    intro j j' hj hj' he
    rw [det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
        (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j) hdet hcolBase,
      det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
        (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j') hdet hcolBase] at he
    have hltab : ∀ q, q < (CR.col sch.N t c).card →
        tab (toff + (Bc + 1) * c + 1 + q) < 2 ^ E.W := by
      intro q hq
      have hmem : tab (toff + (Bc + 1) * c + 1 + q) ∈ CR.col sch.N t c := by
        have himg := (hAt c hcN).2
        rw [← himg]
        exact Finset.mem_image.mpr
          ⟨q, Finset.mem_range.mpr (by rw [(hAt c hcN).1]; exact hq), rfl⟩
      have h2 := hcolrange hmem
      rw [Finset.mem_range] at h2
      omega
    rw [Nat.mod_eq_of_lt (hltab j hj), Nat.mod_eq_of_lt (hltab j' hj')] at he
    exact upTabAt_inj CR Bc tab toff sch.N t c hAt hcN j j' hj hj' he
  have hnd1 : (activeBits (upPairs E i c 1
      (upOwnItems CR Bc colBase (.direct sch t) k base toff))).Nodup :=
    nodup_ownDirect CR E i c k sch.m sch.ℓ (schemeNmax sch) colBase sch.N t base toff Bc
      hW hm hmM hc hbase hbase2 (hperm k c) (hperm 0 c) hbit (by omega) (by omega) (by omega)
      helemB (by
        rw [hdet, upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
        have hsub : (Bc + 1) * c + (colBase + toff) - colBase = toff + (Bc + 1) * c := by omega
        rw [hsub, (hAt c hcN).1]
        exact Nat.mod_eq_of_lt (by omega)) hcardB hinj
  have hnd : (activeBits (upPairs E i c f
      (upOwnItems CR Bc colBase (.direct sch t) k base toff))).Nodup := by
    rw [activeBits_upPairs_mul E i c f _ hf01]
    by_cases h : f = 1
    · rw [if_pos h]
      exact hnd1
    · rw [if_neg h]
      exact List.nodup_nil
  have hval1 : (activeBits (upPairs E i c 1
      (upOwnItems CR Bc colBase (.direct sch t) k base toff))).toFinset
      = bitBlock CR (.direct sch t) lr ({c} : Finset ℕ) base :=
    activeBits_ownDirect_bitBlock (CR := CR) (sch := sch) (t := t) E i c k base toff Bc colBase
      cnt W items tab lr hW hm hmM hc hcN hbase hbase2 (hperm k c) (hperm 0 c) hπε hbit hqnp
      hcoef hdet hAt hcolrange hrows hBcW hcolBase hbig hcardB helemB
  have hval : (activeBits (upPairs E i c f
      (upOwnItems CR Bc colBase (.direct sch t) k base toff))).toFinset
      = if f = 1 then bitBlock CR (.direct sch t) lr ({c} : Finset ℕ) base else ∅ := by
    rw [activeBits_upPairs_mul E i c f _ hf01]
    by_cases h : f = 1
    · rw [if_pos h, if_pos h]
      exact hval1
    · rw [if_neg h, if_neg h, toFinset_nil']
  obtain ⟨h1, -, -⟩ :=
    upFold_own E i c f (upOwnItems CR Bc colBase (.direct sch t) k base toff)
      hWpos hWlt hWw hc hf hfix hbitAll hwtfAll hmulAll hmul2All hwtAll hbitqAll hnd mem hmem a
  rw [h1, hval]
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def UpTabFullAt (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (N t toff : ℕ) : Prop :=
  ∀ c : ℕ, c < N → tab (toff + (Bc + 1) * c) = (CR.col N t c).card ∧
    ∀ q : ℕ, q < Bc → tab (toff + (Bc + 1) * c + 1 + q) =
      ((CR.col N t c).sort (· ≤ ·)).getD q 0
theorem UpTabFullAt.to_set (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (toff N t : ℕ)
    (h : UpTabFullAt CR Bc tab N t toff)
    (hCard : ∀ c, c < N → (CR.col N t c).card ≤ Bc) : UpTabAt CR Bc tab toff N t := by
  apply upTabAt_of_rec CR Bc N t toff tab
  intro c hc
  exact ⟨(h c hc).1, fun q hq => (h c hc).2 q (lt_of_lt_of_le hq (hCard c hc))⟩
theorem sort_getD_le_of_subset (S : Finset ℕ) (R q : ℕ) (h : S ⊆ Finset.range R) :
    (S.sort (· ≤ ·)).getD q 0 ≤ R := by
  classical
  by_cases hq : q < (S.sort (· ≤ ·)).length
  · rw [List.getD_eq_getElem _ _ hq]
    exact Nat.le_of_lt (Finset.mem_range.mp (h ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hq))))
  · have hn : (S.sort (· ≤ ·))[q]? = none := List.getElem?_eq_none_iff.mpr (Nat.not_lt.mp hq)
    change ((S.sort (· ≤ ·))[q]?).getD 0 ≤ R
    rw [hn]
    exact Nat.zero_le _
theorem UpTabFullAt.payload_bounds (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) (toff N t base W : ℕ)
    (h : UpTabFullAt CR Bc tab N t toff)
    (hRange : ∀ c, c < N → CR.col N t c ⊆ Finset.range (CR.rows N t))
    (hBudget : base + CR.rows N t < 2 ^ W) :
    ∀ c, c < N → ∀ j, j < Bc →
      base + tab (toff + (Bc + 1) * c + 1 + j) % 2 ^ W < 2 ^ W := by
  intro c hc j hj
  rw [(h c hc).2 j hj]
  have hrow := sort_getD_le_of_subset (CR.col N t c) (CR.rows N t) j (hRange c hc)
  exact lt_of_le_of_lt (Nat.add_le_add_left ((Nat.mod_le _ _).trans hrow) base) hBudget
theorem env_perm_lt_word (spec : TableSpec) (W : ℕ) (det : ℕ → ℕ) (r : spec.Seed)
    (hFits : spec.Fits W) (k a : ℕ) : (spec.env W det r).perm k a < 2 ^ W := by
  dsimp only [TableSpec.env]
  split_ifs with hk ha
  · exact lt_of_lt_of_le (r.1 ⟨k, hk⟩ ⟨a, ha⟩).isLt (hFits.2.2.1 _ (List.get_mem _ _))
  · exact Nat.two_pow_pos W
  · exact Nat.two_pow_pos W
theorem coefAl_code_singleton (P : HintParams) (E : RAMEnv) (k N X Y c : ℕ)
    (lr : Equiv.Perm (Fin N) × (Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2)) (hcN : c < N) (hm : 0 < P.rows X Y)
    (hPerm : PermAl E k N lr.1) (hCoef : CoefAl P E k N X Y lr.2)
    (s : Fin (P.ell N X Y)) :
    E.coeff k ((E.perm k c % P.rows X Y * P.ell N X Y + s.val) * P.Nmax N X Y +
      E.perm k c / P.rows X Y) =
      ((P.scheme N X Y).code (rowOf0 (P.scheme N X Y) lr.1 hcN hm)
        (lr.2 (rowOf0 (P.scheme N X Y) lr.1 hcN hm))
        ((P.scheme N X Y).rowOf lr {c} (rowOf0 (P.scheme N X Y) lr.1 hcN hm)) s).val := by
  rw [hPerm c hcN]
  have hpos : (lr.1 ⟨c, hcN⟩).val / P.rows X Y < P.Nmax N X Y :=
    div_lt_schemeNmax (P.scheme N X Y) hm (lr.1 ⟨c, hcN⟩).isLt
  have hrow := rowOf_singleton_rowOf0 (sch := P.scheme N X Y) (lr := lr) hcN hm (rowOf0 (P.scheme N X Y) lr.1 hcN hm)
  rw [if_pos rfl] at hrow
  rw [hrow]
  change E.coeff k _ =
    (HintParams.rowBit (lr.2 (rowOf0 (P.scheme N X Y) lr.1 hcN hm))
      {(lr.1 ⟨c, hcN⟩).val / P.rows X Y} s).val
  unfold HintParams.rowBit
  rw [Finset.sum_singleton, dif_pos hpos]
  exact hCoef (rowOf0 (P.scheme N X Y) lr.1 hcN hm) s ⟨_, hpos⟩
theorem up_mul_index_lt (m n j s : ℕ) (hj : j < m) (hs : s < n) : j * n + s < m * n := by
  calc
    j * n + s < j * n + n := Nat.add_lt_add_left hs _
    _ = (j + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right n (by omega)
theorem upDet_width_read (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (hW : 1 < 2 ^ W) : upDet cnt W colBase items tab (1 % 2 ^ W) % 2 ^ W = W := by
  rw [Nat.mod_eq_of_lt hW, upDet_one, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := W))]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
structure UpCrTableFacts (CR : CRFamily) (E : RAMEnv) (Bc colBase : ℕ) (tab : ℕ → ℕ)
    (toff N t base c : ℕ) : Prop where
  base_lt : base < 2 ^ E.W
  rows_le : CR.rows N t ≤ 2 ^ E.W
  bc_lt : Bc < 2 ^ E.W
  at_table : UpTabAt CR Bc tab toff N t
  big : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W
  card : (CR.col N t c).card ≤ Bc
  elem : ∀ j, j < Bc → base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W
theorem upCrTableFacts_of_full (CR : CRFamily) (spec : TableSpec) (W cnt Bc colBase : ℕ)
    (items : List UpIt) (tab : ℕ → ℕ) (rPublic : spec.Seed) (N t base toff c : ℕ)
    (hcN : c < N) (hCol : 4 < colBase) (hEnd : colBase + toff + N * (Bc + 1) < 2 ^ W)
    (hBaseRows : base + CR.rows N t < 2 ^ W) (hFull : UpTabFullAt CR Bc tab N t toff)
    (hCard : ∀ c, c < N → (CR.col N t c).card ≤ Bc)
    (hRange : ∀ c, c < N → CR.col N t c ⊆ Finset.range (CR.rows N t)) :
    UpCrTableFacts CR (spec.env W (upDet cnt W colBase items tab) rPublic) Bc colBase tab toff N t base c := by
  let E := spec.env W (upDet cnt W colBase items tab) rPublic
  change UpCrTableFacts CR E Bc colBase tab toff N t base c
  have hrow := Nat.mul_le_mul_right (Bc + 1) (Nat.succ_le_of_lt hcN)
  have hBig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ W := by
    calc
      (Bc + 1) * c + (colBase + toff) + Bc + 1 = colBase + toff + (c + 1) * (Bc + 1) := by ring
      _ ≤ colBase + toff + N * (Bc + 1) := Nat.add_le_add_left hrow _
      _ < 2 ^ W := hEnd
  have hRows : CR.rows N t ≤ 2 ^ W := by omega
  have hBc : Bc < 2 ^ W := by omega
  refine ⟨lt_of_le_of_lt (Nat.le_add_right _ _) hBaseRows, hRows, hBc,
    UpTabFullAt.to_set CR Bc tab toff N t hFull hCard, hBig, hCard c hcN, ?_⟩
  intro j hj
  rw [det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
    (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j) rfl hCol]
  exact UpTabFullAt.payload_bounds CR Bc tab toff N t base W hFull hRange hBaseRows c hcN j hj
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upLocal_direct_of_table (CR : CRFamily) (P : HintParams) (spec : TableSpec)
    (W cnt Bc colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) (rPublic : spec.Seed)
    (i N X Y t k base toff : ℕ)
    (lr : Equiv.Perm (Fin N) × (Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2))
    (hW : 1 < 2 ^ W) (hWpos : 0 < W) (hFits : spec.Fits W)
    (hm : 0 < P.rows X Y) (hCol : 4 < colBase)
    (hPerm : PermAl (spec.env W (upDet cnt W colBase items tab) rPublic) k N lr.1)
    (hCoef : CoefAl P (spec.env W (upDet cnt W colBase items tab) rPublic) k N X Y lr.2)
    (hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ W)
    (hEnd : colBase + toff + N * (Bc + 1) < 2 ^ W)
    (hAll : base + P.rows X Y * P.ell N X Y + CR.rows N t < 2 ^ W)
    (hFull : UpTabFullAt CR Bc tab N t toff)
    (hCard : ∀ c, c < N → (CR.col N t c).card ≤ Bc)
    (hRange : ∀ c, c < N → CR.col N t c ⊆ Finset.range (CR.rows N t)) :
    UpLocalBitsCorrect CR (spec.env W (upDet cnt W colBase items tab) rPublic)
      i Bc colBase (.direct (P.scheme N X Y) t) lr k base toff := by
  let E := spec.env W (upDet cnt W colBase items tab) rPublic
  change UpLocalBitsCorrect CR E i Bc colBase (.direct (P.scheme N X Y) t) lr k base toff
  intro c f hcN hc hf hf01 mem hmem a
  change c < N at hcN
  have hBase2 : base + P.rows X Y * P.ell N X Y < 2 ^ W := by omega
  have hBase : base < 2 ^ W := by omega
  have hEll : 1 ≤ P.ell N X Y := by unfold HintParams.ell; omega
  have hMell : P.rows X Y ≤ P.rows X Y * P.ell N X Y := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (P.rows X Y) hEll
  have hmW : P.rows X Y ≤ 2 ^ W := by omega
  have hpermN : E.perm k c < N := by rw [hPerm c hcN]; exact (lr.1 ⟨c, hcN⟩).isLt
  have hpos : E.perm k c / P.rows X Y < P.Nmax N X Y :=
    div_lt_schemeNmax (P.scheme N X Y) hm hpermN
  have hbit : ∀ s, s < P.ell N X Y → base + (E.perm k c % P.rows X Y * P.ell N X Y + s) < 2 ^ W := by
    intro s hs
    exact (Nat.add_lt_add_left (up_mul_index_lt (P.rows X Y) (P.ell N X Y)
      (E.perm k c % P.rows X Y) s (Nat.mod_lt _ hm) hs) base).trans hBase2
  have hIndex : ∀ s : Fin (P.ell N X Y),
      (E.perm k c % P.rows X Y * P.ell N X Y + s.val) * P.Nmax N X Y + E.perm k c / P.rows X Y < 2 ^ W := by
    intro s
    have hcol := up_mul_index_lt (P.rows X Y) (P.ell N X Y) (E.perm k c % P.rows X Y) s.val
      (Nat.mod_lt _ hm) s.isLt
    exact (up_mul_index_lt (P.rows X Y * P.ell N X Y) (P.Nmax N X Y)
      (E.perm k c % P.rows X Y * P.ell N X Y + s.val) (E.perm k c / P.rows X Y) hcol hpos).trans_le hShape
  have hC := upCrTableFacts_of_full CR spec W cnt Bc colBase items tab rPublic N t
    (base + P.rows X Y * P.ell N X Y) toff c hcN hCol hEnd hAll hFull hCard hRange
  have hWW : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W := upDet_width_read cnt W colBase items tab hW
  have hh := upFold_node_direct (sch := P.scheme N X Y) (t := t)
    CR E i base c f a lr k toff Bc colBase 0 cnt W items tab
    hW hWpos (Nat.lt_two_pow_self (n := W)) hWW hc hf hf01
    (env_perm_lt_word spec W _ rPublic hFits) hm hmW hcN hBase hBase2
    (hPerm c hcN) hbit hIndex
    (coefAl_code_singleton P E k N X Y c lr hcN hm hPerm hCoef)
    rfl hC.at_table (hRange c hcN) hC.rows_le hC.bc_lt hCol hC.big hC.card hC.elem mem hmem
  simpa only [upKids, List.append_nil, upNodeLocalBits] using hh
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
theorem upStoreIt_apply (E : RAMEnv) (i N base : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hN : 0 < N) (hNM : N ≤ 2 ^ E.W) (hc : ab.c < 2 ^ E.W)
    (hf : ab.f < 2 ^ E.W) (hbase : base < 2 ^ E.W) (hbit : base + ab.c % N < 2 ^ E.W) :
    upvCn E i (upStoreIt N base) ab = ab.c ∧
      upvFn E i (upStoreIt N base) ab = ab.f ∧
      upvBit E i (upStoreIt N base) ab = base + ab.c % N ∧
      upvWt E i (upStoreIt N base) ab = 1 := by
  have hlt : ab.c % N < 2 ^ E.W := by
    have h := Nat.mod_lt ab.c hN
    omega
  have hset0 : (upStoreIt N base).setSt = 0 := rfl
  have hfrom0 : (upStoreIt N base).fromI = 0 := rfl
  have hsrc1 : (upStoreIt N base).srcC = 1 := rfl
  have hkp0 : (upStoreIt N base).kp = 0 := rfl
  have hm : (upStoreIt N base).m = N := rfl
  have hell1 : (upStoreIt N base).ell = 1 := rfl
  have hs0 : (upStoreIt N base).s = 0 := rfl
  have hmode0 : (upStoreIt N base).mode = 0 := rfl
  have huse0 : (upStoreIt N base).useC = 0 := rfl
  have hbase0 : (upStoreIt N base).base = base := rfl
  have hZ2 : upvZ2 E i (upStoreIt N base) = 0 := by
    simp only [upvZ2, hfrom0, Nat.zero_mul, Nat.zero_mod]
  have hZ3 : upvZ3 E (upStoreIt N base) = 1 := by
    simp only [upvZ3, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ4 : upvZ4 E (upStoreIt N base) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ4, upvZ1, hkp0, hZ3, Nat.mul_one, Nat.mod_mod]
  have hZ5 : upvZ5 E i (upStoreIt N base) ab = E.perm 0 ab.c % 2 ^ E.W := by
    simp only [upvZ5, hZ4, hZ2, Nat.add_zero, Nat.mod_mod]
  have hZ6 : upvZ6 E (upStoreIt N base) ab = ab.c := by
    simp only [upvZ6, hsrc1, one_mul, Nat.mod_eq_of_lt hc]
  have hZ7 : upvZ7 E (upStoreIt N base) = 0 := by
    simp only [upvZ7, hsrc1, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have hZ8 : upvZ8 E i (upStoreIt N base) ab = 0 := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_zero, Nat.zero_mod]
  have hImg : upvImg E i (upStoreIt N base) ab = ab.c := by
    simp only [upvImg, hZ8, hZ6, Nat.zero_add, Nat.mod_eq_of_lt hc]
  have hJ0 : upvJ0 E i (upStoreIt N base) ab = ab.c % N := by
    simp only [upvJ0, hImg, hm]
    rw [Nat.mod_eq_of_lt hlt]
  have hY2 : upvY2 E i (upStoreIt N base) ab = 0 := by
    simp only [upvY2, hset0, Nat.mul_zero, Nat.zero_mod]
  have hCn : upvCn E i (upStoreIt N base) ab = ab.c := by
    simp only [upvCn, hY2, Nat.add_zero, Nat.mod_eq_of_lt hc]
  have hY11 : upvY11 E i (upStoreIt N base) ab = 0 := by
    simp only [upvY11, hset0, Nat.mul_zero, Nat.zero_mod]
  have hFn : upvFn E i (upStoreIt N base) ab = ab.f := by
    simp only [upvFn, hY11, Nat.add_zero, Nat.mod_eq_of_lt hf]
  have hX1 : upvX1 E (upStoreIt N base) = 1 := by
    simp only [upvX1, huse0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hX2 : upvX2 E i (upStoreIt N base) ab = 0 := by
    simp only [upvX2, huse0, Nat.zero_mul, Nat.zero_mod]
  have hW0 : upvW0 E i (upStoreIt N base) ab = 1 := by
    simp only [upvW0, hX2, hX1, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hX10 : upvX10 E i (upStoreIt N base) ab = 0 := by
    simp only [upvX10, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hWt : upvWt E i (upStoreIt N base) ab = 1 := by
    simp only [upvWt, hX10, hW0, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hY3 : upvY3 E i (upStoreIt N base) ab = ab.c % N := by
    simp only [upvY3, hJ0, hell1, Nat.mul_one, Nat.mod_eq_of_lt hlt]
  have hQ : upvQ E i (upStoreIt N base) ab = ab.c % N := by
    simp only [upvQ, hY3, hs0, Nat.add_zero, Nat.mod_eq_of_lt hlt]
  have hX7 : upvX7 E i (upStoreIt N base) ab = 0 := by
    simp only [upvX7, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hX8 : upvX8 E i (upStoreIt N base) ab = base := by
    simp only [upvX8, hX7, hbase0, Nat.zero_add, Nat.mod_eq_of_lt hbase]
  have hBit : upvBit E i (upStoreIt N base) ab = base + ab.c % N := by
    simp only [upvBit, hX8, hQ, Nat.mod_eq_of_lt hbit]
  exact ⟨hCn, hFn, hBit, hWt⟩
@[simp] theorem upSave_setSt (sav : ℕ) : (upSave sav).setSt = 0 := rfl
@[simp] theorem upSave_mode (sav : ℕ) : (upSave sav).mode = 2 := rfl
@[simp] theorem upSave_mOn (sav : ℕ) : (upSave sav).mOn = 0 := rfl
@[simp] theorem upSave_sav (sav : ℕ) : (upSave sav).sav = sav := rfl
@[simp] theorem upRestore_setSt (sav : ℕ) : (upRestore sav).setSt = 1 := rfl
@[simp] theorem upRestore_mode (sav : ℕ) : (upRestore sav).mode = 3 := rfl
@[simp] theorem upRestore_mOn (sav : ℕ) : (upRestore sav).mOn = 0 := rfl
@[simp] theorem upRestore_sav (sav : ℕ) : (upRestore sav).sav = sav := rfl
def upOwn (Bc : ℕ) : Node → ℕ
  | .store _ => 0
  | .cr N _ => N * (Bc + 1)
  | .direct sch _ => sch.N * (Bc + 1)
  | .recursive sch _ _ _ _ => sch.N * (Bc + 1)
theorem take_sum_succ_node (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (s : ℕ)
    (hs : s < sch.ℓ) :
    ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take (s + 1)).sum
      = ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s).sum
        + upTabLen Bc (child ⟨s, hs⟩) :=
  take_sum_succ_ofFn (fun i : Fin sch.ℓ => upTabLen Bc (child i)) s hs
theorem take_sum_full_node (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) :
    ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take sch.ℓ).sum
      = ∑ s : Fin sch.ℓ, upTabLen Bc (child s) :=
  take_sum_full_ofFn (fun i : Fin sch.ℓ => upTabLen Bc (child i))
def upKidOff (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff s : ℕ) : ℕ :=
  toff + sch.N * (Bc + 1) + ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s).sum
theorem upKidOff_succ (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff s : ℕ)
    (hs : s < sch.ℓ) :
    upKidOff Bc sch child toff (s + 1)
      = upKidOff Bc sch child toff s + upTabLen Bc (child ⟨s, hs⟩) := by
  unfold upKidOff
  rw [take_sum_succ_node Bc sch child s hs]
  omega
theorem upKidOff_mono (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff s s' : ℕ)
    (h : s ≤ s') : upKidOff Bc sch child toff s ≤ upKidOff Bc sch child toff s' := by
  unfold upKidOff
  have h' := take_sum_mono (List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)) s s' h
  omega
theorem upKidOff_full (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff : ℕ) :
    upKidOff Bc sch child toff sch.ℓ
      = toff + (sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s)) := by
  unfold upKidOff
  rw [take_sum_full_node]
  omega
theorem upKidOff_le_top (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff s : ℕ)
    (hs : s < sch.ℓ) :
    upKidOff Bc sch child toff s + upTabLen Bc (child ⟨s, hs⟩)
      ≤ toff + (sch.N * (Bc + 1) + ∑ i : Fin sch.ℓ, upTabLen Bc (child i)) := by
  rw [← upKidOff_succ Bc sch child toff s hs]
  calc upKidOff Bc sch child toff (s + 1)
      ≤ upKidOff Bc sch child toff sch.ℓ := upKidOff_mono Bc sch child toff (s + 1) sch.ℓ (by omega)
    _ = toff + (sch.N * (Bc + 1) + ∑ i : Fin sch.ℓ, upTabLen Bc (child i)) :=
        upKidOff_full Bc sch child toff
theorem upOwn_le_tabLen (Bc : ℕ) : ∀ (T : Node), upOwn Bc T ≤ upTabLen Bc T
  | .store _ => by simp [upOwn, upTabLen]
  | .cr N _ => by simp [upOwn, upTabLen]
  | .direct sch _ => by simp [upOwn, upTabLen]
  | .recursive sch _ _ _ _ => by simp only [upOwn, upTabLen]; omega
theorem activeBits_ownStore (E : RAMEnv) (i N base c : ℕ)
    (hW : 1 < 2 ^ E.W) (hN : 0 < N) (hNM : N ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hbit : base + c % N < 2 ^ E.W) :
    activeBits (upPairs E i c 1 [upStoreIt N base]) = [base + c % N] := by
  obtain ⟨-, -, hBit, hWt⟩ :=
    upStoreIt_apply E i N base (⟨fun _ => 0, c, 1⟩ : UpAbs) hW hN hNM hc (by omega) hbase hbit
  have hmOn : (upStoreIt N base).mOn = 1 := rfl
  have hpair : (upvBit E i (upStoreIt N base) (⟨fun _ => 0, c, 1⟩ : UpAbs),
      upvWt E i (upStoreIt N base) (⟨fun _ => 0, c, 1⟩ : UpAbs) * 1
        * (upStoreIt N base).mOn) = (base + c % N, 1) := by
    rw [hBit, hWt, hmOn]
  simp only [activeBits, upPairs, List.map_cons, List.map_nil, List.filter_cons,
    List.filter_nil, hpair]
  norm_num
theorem activeBits_ownStore_gated (E : RAMEnv) (i N base c f : ℕ)
    (hW : 1 < 2 ^ E.W) (hN : 0 < N) (hNM : N ≤ 2 ^ E.W) (hc : c < 2 ^ E.W)
    (hbase : base < 2 ^ E.W) (hbit : base + c % N < 2 ^ E.W) (hf : f = 0 ∨ f = 1) :
    activeBits (upPairs E i c f [upStoreIt N base])
      = if f = 1 then [base + c % N] else [] := by
  rw [activeBits_upPairs_mul E i c f _ hf,
    activeBits_ownStore E i N base c hW hN hNM hc hbase hbit]
theorem bitBlock_store {CR : CRFamily} (N : ℕ) (r : Node.Seed (.store N)) (x : Finset ℕ)
    (base : ℕ) :
    bitBlock CR (.store N) r x base = (x.filter (fun a => a < N)).image (fun a => base + a) := by
  ext a
  rw [mem_bitBlock]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpx : (p.val : ℕ) ∈ x := by
      by_contra hc
      rw [show bitVal CR (.store N) r p x = 0 from by simp only [bitVal]; rw [if_neg hc]] at hp
      exact zero_ne_one hp
    have hlt : p.val < N := by
      have h := p.isLt
      simp only [synLen] at h
      exact h
    exact Finset.mem_image.mpr ⟨p.val, Finset.mem_filter.mpr ⟨hpx, hlt⟩, rfl⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hvx, hvN⟩ := Finset.mem_filter.mp hv
    refine ⟨⟨v, hvN⟩, ?_, rfl⟩
    simp only [bitVal]
    rw [if_pos hvx]
theorem toFinset_singleton' (a : ℕ) : ([a] : List ℕ).toFinset = {a} := by
  rw [List.toFinset_cons, List.toFinset_nil]
  rfl
theorem activeBits_ownStore_bitBlock {CR : CRFamily} (E : RAMEnv) (i N base c f : ℕ)
    (r : Node.Seed (.store N)) (k toff Bc colBase : ℕ)
    (hW : 1 < 2 ^ E.W) (hN : 0 < N) (hNM : N ≤ 2 ^ E.W)
    (hc : c < 2 ^ E.W) (hcN : c < N) (hbase : base < 2 ^ E.W)
    (hbit : base + c % N < 2 ^ E.W) (hf : f = 0 ∨ f = 1) :
    (activeBits (upPairs E i c f (upOwnItems CR Bc colBase (.store N) k base toff))).toFinset
      = if f = 1 then bitBlock CR (.store N) r ({c} : Finset ℕ) base else ∅ := by
  have hown : upOwnItems CR Bc colBase (.store N) k base toff = [upStoreIt N base] := by
    simp only [upOwnItems]
  have hblk : bitBlock CR (.store N) r ({c} : Finset ℕ) base = {base + c} := by
    rw [bitBlock_store]
    have h1 : ({c} : Finset ℕ).filter (fun a => a < N) = {c} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, -⟩
        rfl
      · intro h
        subst h
        exact ⟨rfl, hcN⟩
    rw [h1, Finset.image_singleton]
  rw [hown, activeBits_ownStore_gated E i N base c f hW hN hNM hc hbase hbit hf, hblk]
  by_cases h : f = 1
  · rw [if_pos h, if_pos h, Nat.mod_eq_of_lt hcN, toFinset_singleton']
  · rw [if_neg h, if_neg h, toFinset_nil']
theorem getElem_eq_of_getElem?_eq_some {α : Type} {l : List α} {i : ℕ} {x : α}
    (h : l[i]? = some x) (hi : i < l.length) : l[i]'hi = x := by
  have h2 : l[i]? = some (l[i]'hi) := List.getElem?_eq_getElem hi
  rw [h] at h2
  exact (Option.some.inj h2).symm
theorem permSizesOf_get? (R : Node) (k : ℕ) :
    (permSizesOf R)[k]? = ((schemeNodes R)[k]?).map Node.N := by
  simp only [permSizesOf, List.getElem?_map]
theorem coeffShapesOf_get? (R : Node) (k : ℕ) :
    (coeffShapesOf R)[k]? = ((schemeNodes R)[k]?).map nodeCoins := by
  simp only [coeffShapesOf, List.getElem?_map]
theorem zmod2_val_natCast {m : ℕ} (hm : m < 2) : ((m : ZMod 2)).val = m := by
  have h : m = 0 ∨ m = 1 := by omega
  rcases h with rfl | rfl
  · exact ZMod.val_zero
  · exact ZMod.val_one 2
def BlockOf (R : Node) (k : ℕ) (L : List Node) : Prop :=
  ∀ j, j < L.length → (schemeNodes R)[k + j]? = L[j]?
theorem lt_length_of_getElem?_eq_some {α : Type u} {l : List α} {i : ℕ} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  by_contra hc
  rw [Nat.not_lt] at hc
  rw [List.getElem?_eq_none_iff.mpr hc] at h
  exact absurd h (by simp)
theorem BlockOf_head {R : Node} {k : ℕ} {T : Node} {l : List Node}
    (h : BlockOf R k (T :: l)) : (schemeNodes R)[k]? = some T := by
  have h0 := h 0 (by simp)
  simpa using h0
theorem permSizes_get_of_block {R T : Node} {k : ℕ}
    (h : (schemeNodes R)[k]? = some T) :
    ∃ hk : k < (hintSpec R).permSizes.length,
      (hintSpec R).permSizes.get ⟨k, hk⟩ = T.N := by
  have hlt : k < (schemeNodes R).length := lt_length_of_getElem?_eq_some h
  have hk : k < (hintSpec R).permSizes.length := by
    show k < (permSizesOf R).length
    simpa only [permSizesOf, List.length_map] using hlt
  refine ⟨hk, ?_⟩
  have hget : (hintSpec R).permSizes[k]? = some T.N := by
    show (permSizesOf R)[k]? = some T.N
    rw [permSizesOf_get?, h]
    rfl
  exact getElem_eq_of_getElem?_eq_some hget hk
theorem coeffShapes_get_of_block {R T : Node} {k : ℕ}
    (h : (schemeNodes R)[k]? = some T) :
    ∃ hk : k < (hintSpec R).coeffShapes.length,
      (hintSpec R).coeffShapes.get ⟨k, hk⟩ = nodeCoins T := by
  have hlt : k < (schemeNodes R).length := lt_length_of_getElem?_eq_some h
  have hk : k < (hintSpec R).coeffShapes.length := by
    show k < (coeffShapesOf R).length
    simpa only [coeffShapesOf, List.length_map] using hlt
  refine ⟨hk, ?_⟩
  have hget : (hintSpec R).coeffShapes[k]? = some (nodeCoins T) := by
    show (coeffShapesOf R)[k]? = some (nodeCoins T)
    rw [coeffShapesOf_get?, h]
    rfl
  exact getElem_eq_of_getElem?_eq_some hget hk
theorem getElem?_flatten_ofFn' {α : Type u} :
    ∀ (n : ℕ) (f : Fin n → List α) (s : Fin n) (j : ℕ), j < (f s).length →
      (List.ofFn f).flatten[((List.ofFn fun i : Fin n => (f i).length).take s.val).sum + j]?
        = (f s)[j]? := by
  intro n
  induction n with
  | zero => intro f s; exact absurd s.isLt (Nat.not_lt_zero _)
  | succ n ih =>
      intro f s
      refine Fin.cases ?_ ?_ s
      · intro j hj
        simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, List.take_zero,
          List.sum_nil, Nat.zero_add]
        exact List.getElem?_append_left hj
      · intro s' j hj
        simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons]
        rw [List.getElem?_append_right (by omega)]
        have hsub : (f 0).length
              + (List.take (↑s') (List.ofFn fun i : Fin n => (f i.succ).length)).sum + j
              - (f 0).length
            = (List.take (↑s') (List.ofFn fun i : Fin n => (f i.succ).length)).sum + j := by omega
        rw [hsub]
        exact ih (fun i : Fin n => f (Fin.succ i)) s' j hj
theorem BlockOf_child {R : Node} {k : ℕ} {sch : RowScheme} {t : ℕ} {Xs Ys : Fin sch.ℓ → ℕ}
    {child : Fin sch.ℓ → Node}
    (hb : BlockOf R k (schemeNodes (.recursive sch t Xs Ys child))) (s : Fin sch.ℓ) :
    BlockOf R
      (k + 1 + ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
      (schemeNodes (child s)) := by
  intro j hj
  have hget : (List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length)[s.val]?
      = some (schemeNodes (child s)).length :=
    getElem?_ofFn' (fun i : Fin sch.ℓ => (schemeNodes (child i)).length) s
  have hle := take_sum_add_getElem_le
    (List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length) s.val
    (schemeNodes (child s)).length hget
  have hlen : 1 + ((List.ofFn fun i : Fin sch.ℓ =>
      (schemeNodes (child i)).length).take s.val).sum + j
      < (schemeNodes (.recursive sch t Xs Ys child)).length := by
    rw [schemeNodes_recursive, List.length_append, List.length_singleton,
      flatten_length_eq_sum]
    omega
  have hidx : (k + 1 + ((List.ofFn fun i : Fin sch.ℓ =>
      (schemeNodes (child i)).length).take s.val).sum) + j
      = k + (1 + ((List.ofFn fun i : Fin sch.ℓ =>
        (schemeNodes (child i)).length).take s.val).sum + j) := by omega
  rw [hidx, hb _ hlen, schemeNodes_recursive]
  rw [List.getElem?_append_right (l₁ := [Node.recursive sch t Xs Ys child])
    (by simp only [List.length_singleton]; omega)]
  simp only [List.length_singleton]
  have hsub : 1 + ((List.ofFn fun i : Fin sch.ℓ =>
      (schemeNodes (child i)).length).take s.val).sum + j - 1
      = ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum + j := by
    omega
  rw [hsub]
  exact getElem?_flatten_ofFn' sch.ℓ (fun i : Fin sch.ℓ => schemeNodes (child i)) s j hj
theorem column_singleton {sch : RowScheme} {c : ℕ} (lr : sch.LocalSeed) (hcN : c < sch.N)
    (hm : 0 < sch.m) (s : Fin sch.ℓ) :
    sch.column lr ({c} : Finset ℕ) s
      = if sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
            {(lr.1 ⟨c, hcN⟩).val / sch.m} s = 1
        then {(rowOf0 sch lr.1 hcN hm).val} else ∅ := by
  unfold RowScheme.column RowScheme.rowsWhere
  classical
  have hpred : ∀ j : Fin sch.m,
      (sch.code j (lr.2 j) (sch.rowOf lr ({c} : Finset ℕ) j) s = 1)
        ↔ (j = rowOf0 sch lr.1 hcN hm ∧
            sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
              {(lr.1 ⟨c, hcN⟩).val / sch.m} s = 1) := by
    intro j
    rw [rowOf_singleton_rowOf0 (lr := lr) hcN hm j]
    by_cases hj : j = rowOf0 sch lr.1 hcN hm
    · subst hj
      simp
    · rw [if_neg hj, code_empty]
      simp [hj]
  by_cases h1 : sch.code (rowOf0 sch lr.1 hcN hm) (lr.2 (rowOf0 sch lr.1 hcN hm))
      {(lr.1 ⟨c, hcN⟩).val / sch.m} s = 1
  · rw [if_pos h1]
    ext a
    rw [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter] at hj
      exact congrArg Fin.val ((hpred j).mp hj.2).1
    · rintro rfl
      refine ⟨_, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hpred _).mpr ⟨rfl, h1⟩
  · rw [if_neg h1]
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    rintro a hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨j, hj, -⟩ := hmem
    simp only [Finset.mem_filter] at hj
    exact absurd ((hpred j).mp hj.2).2 h1
theorem upFold_node_store (CR : CRFamily) (E : RAMEnv) (i N base c f a : ℕ)
    (r : Node.Seed (.store N)) (k toff Bc colBase sav : ℕ)
    (hW : 1 < 2 ^ E.W) (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hN : 0 < N) (hNM : N ≤ 2 ^ E.W) (hc : c < 2 ^ E.W) (hcN : c < N)
    (hf : f < 2 ^ E.W) (hf01 : f = 0 ∨ f = 1)
    (hbase : base < 2 ^ E.W) (hbit : base + c % N < 2 ^ E.W)
    (mem : ℕ → ℕ) (hmem : ∀ x, mem x < 2 ^ E.W) :
    (upFold E i ⟨mem, c, f⟩
        (upOwnItems CR Bc colBase (.store N) k base toff
          ++ upKids CR Bc colBase (.store N) k base toff sav [])).mem a
      = mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.store N) r {c} base else ∅) a := by
  have hown : upOwnItems CR Bc colBase (.store N) k base toff = [upStoreIt N base] := rfl
  have hkid : upKids CR Bc colBase (.store N) k base toff sav ([] : List UpIt) = [] := rfl
  rw [hkid, List.append_nil, hown]
  obtain ⟨-, -, hBit, hWt⟩ :=
    upStoreIt_apply E i N base (⟨fun _ => 0, c, f⟩ : UpAbs) hW hN hNM hc hf hbase hbit
  have hmOn : (upStoreIt N base).mOn = 1 := rfl
  have hbitAll : ∀ it ∈ [upStoreIt N base], ∀ m : ℕ → ℕ,
      upvBit E i it (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W := by
    intro it hit m
    rw [List.mem_singleton] at hit
    subst hit
    rw [upvBit_mem_irrel E i (upStoreIt N base) c f m (fun _ => 0), hBit]
    exact hbit
  have hwtAll : ∀ it ∈ [upStoreIt N base], ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W := by
    intro it hit m
    rw [List.mem_singleton] at hit
    subst hit
    rw [upvWt_mem_irrel E i (upStoreIt N base) c f m (fun _ => 0), hWt, Nat.one_mul]
    exact hf
  have hmulAll : ∀ it ∈ [upStoreIt N base], ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 ^ E.W := by
    intro it hit m
    rw [List.mem_singleton] at hit
    subst hit
    rw [upvWt_mem_irrel E i (upStoreIt N base) c f m (fun _ => 0), hWt, hmOn, Nat.one_mul,
      Nat.mul_one]
    exact hf
  have hmul2All : ∀ it ∈ [upStoreIt N base], ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 := by
    intro it hit m
    rw [List.mem_singleton] at hit
    subst hit
    rw [upvWt_mem_irrel E i (upStoreIt N base) c f m (fun _ => 0), hWt, hmOn, Nat.one_mul,
      Nat.mul_one]
    rcases hf01 with h | h <;> omega
  have hwtP : ∀ q ∈ upPairs E i c f [upStoreIt N base], q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    rw [upPairs, List.mem_map] at hq
    obtain ⟨it, hit, rfl⟩ := hq
    rw [List.mem_singleton] at hit
    subst hit
    rw [hWt, hmOn, Nat.one_mul, Nat.mul_one]
    exact hf01
  have hbitq : ∀ q ∈ upPairs E i c f [upStoreIt N base], q.1 < 2 ^ E.W := by
    intro q hq
    rw [upPairs, List.mem_map] at hq
    obtain ⟨it, hit, rfl⟩ := hq
    rw [List.mem_singleton] at hit
    subst hit
    rw [hBit]
    exact hbit
  have hnd : (activeBits (upPairs E i c f [upStoreIt N base])).Nodup := by
    rw [activeBits_ownStore_gated E i N base c f hW hN hNM hc hbase hbit hf01]
    by_cases h : f = 1
    · rw [if_pos h]
      exact List.nodup_singleton _
    · rw [if_neg h]
      exact List.nodup_nil
  obtain ⟨h1, -, -⟩ :=
    upFold_own E i c f [upStoreIt N base] hWpos hWlt hWw hc hf
      (by intro it hit; rw [List.mem_singleton] at hit; subst hit; exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩)
      hbitAll hwtAll hmulAll hmul2All hwtP hbitq hnd mem hmem a
  rw [h1, ← hown, activeBits_ownStore_bitBlock E i N base c f r k toff Bc colBase hW hN hNM hc
    hcN hbase hbit hf01]
theorem upFold_node_cr (CR : CRFamily) (E : RAMEnv) (i N t base c f a : ℕ)
    (r : Node.Seed (.cr N t)) (k toff Bc colBase sav : ℕ)
    (cnt W : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hWpos : 0 < E.W) (hWlt : E.W < 2 ^ E.W)
    (hWw : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W)
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) (hf01 : f = 0 ∨ f = 1)
    (hperm : ∀ k a, E.perm k a < 2 ^ E.W)
    (hbase : base < 2 ^ E.W)
    (hdet : E.det = upDet cnt W colBase items tab)
    (hAt : UpTabAt CR Bc tab toff N t)
    (hcolrange : CR.col N t c ⊆ Finset.range (CR.rows N t))
    (hrows : CR.rows N t ≤ 2 ^ E.W) (hBcW : Bc < 2 ^ E.W) (hcolBase : 4 < colBase)
    (hcN : c < N)
    (hbig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ E.W)
    (hcardB : (CR.col N t c).card ≤ Bc)
    (helemB : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W)
    (mem : ℕ → ℕ) (hmem : ∀ x, mem x < 2 ^ E.W) :
    (upFold E i ⟨mem, c, f⟩
        (upOwnItems CR Bc colBase (.cr N t) k base toff
          ++ upKids CR Bc colBase (.cr N t) k base toff sav [])).mem a
      = mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.cr N t) r {c} base else ∅) a := by
  have hown : upOwnItems CR Bc colBase (.cr N t) k base toff
      = (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) base j) := rfl
  have hkid : upKids CR Bc colBase (.cr N t) k base toff sav ([] : List UpIt) = [] := rfl
  rw [hkid, List.append_nil]
  have hcard : E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W = (CR.col N t c).card := by
    rw [hdet, upDet_tab cnt W colBase items tab _ (by omega) (by omega)]
    have hsub : (Bc + 1) * c + (colBase + toff) - colBase = toff + (Bc + 1) * c := by omega
    rw [hsub, (hAt c hcN).1]
    exact Nat.mod_eq_of_lt (by omega)
  have hpoint : ∀ j, j < Bc →
      upvBit E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs)
          = base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W ∧
        upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs) * f
          < 2 := by
    intro j hj
    have htb : (Bc + 1) * c + (colBase + toff) < 2 ^ E.W := by omega
    have hjc : (Bc + 1) * c + (colBase + toff) + j < 2 ^ E.W := by omega
    have hjb : (Bc + 1) * c + (colBase + toff) + j + 1 < 2 ^ E.W := by omega
    have helem : E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W + base < 2 ^ E.W := by
      have := helemB j hj
      omega
    obtain ⟨-, -, hBit, hWt, hVal⟩ :=
      upCrIt_apply E i (colBase + toff) (Bc + 1) base j (⟨fun _ => 0, c, f⟩ : UpAbs)
        hW hc hf hbase htb hjc hjb helem (hperm 0 c)
    have hmOn : (upCrIt (colBase + toff) (Bc + 1) base j).mOn = 1 := rfl
    have hVal' : upvValid E i (upCrIt (colBase + toff) (Bc + 1) base j)
        (⟨fun _ => 0, c, f⟩ : UpAbs)
        = if j < E.det ((Bc + 1) * c + (colBase + toff)) % 2 ^ E.W then 1 else 0 := hVal
    have hBit' : upvBit E i (upCrIt (colBase + toff) (Bc + 1) base j)
        (⟨fun _ => 0, c, f⟩ : UpAbs)
        = base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W := hBit
    refine ⟨hBit', ?_⟩
    rw [hWt, hVal', hcard]
    by_cases hjc' : j < (CR.col N t c).card
    · rw [if_pos hjc', Nat.one_mul]
      rcases hf01 with h | h <;> rw [h] <;> norm_num
    · rw [if_neg hjc', Nat.zero_mul]
      norm_num
  have hfix : ∀ it ∈ upOwnItems CR Bc colBase (.cr N t) k base toff,
      it.setSt = 0 ∧ it.mode < 2 := by
    intro it hit
    rw [hown, List.mem_map] at hit
    obtain ⟨j, -, rfl⟩ := hit
    exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
  have hbit : ∀ it ∈ upOwnItems CR Bc colBase (.cr N t) k base toff, ∀ m : ℕ → ℕ,
      upvBit E i it (⟨m, c, f⟩ : UpAbs) < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_map] at hit
    obtain ⟨j, hj, rfl⟩ := hit
    have hjB : j < Bc := List.mem_range.mp hj
    rw [upvBit_mem_irrel E i _ c f m (fun _ => 0), (hpoint j hjB).1]
    exact helemB j hjB
  have hwtf : ∀ it ∈ upOwnItems CR Bc colBase (.cr N t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_map] at hit
    obtain ⟨j, hj, rfl⟩ := hit
    have hjB : j < Bc := List.mem_range.mp hj
    have heq : upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨m, c, f⟩ : UpAbs)
        = upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs) :=
      upvWt_mem_irrel E i _ c f m (fun _ => 0)
    rw [heq]
    have h2 := (hpoint j hjB).2
    omega
  have hmul : ∀ it ∈ upOwnItems CR Bc colBase (.cr N t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 ^ E.W := by
    intro it hit m
    rw [hown, List.mem_map] at hit
    obtain ⟨j, hj, rfl⟩ := hit
    have hjB : j < Bc := List.mem_range.mp hj
    have heq : upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨m, c, f⟩ : UpAbs)
        = upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs) :=
      upvWt_mem_irrel E i _ c f m (fun _ => 0)
    have hmOn : (upCrIt (colBase + toff) (Bc + 1) base j).mOn = 1 := rfl
    rw [heq, hmOn, Nat.mul_one]
    have h2 := (hpoint j hjB).2
    omega
  have hmul2 : ∀ it ∈ upOwnItems CR Bc colBase (.cr N t) k base toff, ∀ m : ℕ → ℕ,
      upvWt E i it (⟨m, c, f⟩ : UpAbs) * f * it.mOn < 2 := by
    intro it hit m
    rw [hown, List.mem_map] at hit
    obtain ⟨j, hj, rfl⟩ := hit
    have hjB : j < Bc := List.mem_range.mp hj
    have heq : upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨m, c, f⟩ : UpAbs)
        = upvWt E i (upCrIt (colBase + toff) (Bc + 1) base j) (⟨fun _ => 0, c, f⟩ : UpAbs) :=
      upvWt_mem_irrel E i _ c f m (fun _ => 0)
    have hmOn : (upCrIt (colBase + toff) (Bc + 1) base j).mOn = 1 := rfl
    rw [heq, hmOn, Nat.mul_one]
    exact (hpoint j hjB).2
  have hwt : ∀ q ∈ upPairs E i c f (upOwnItems CR Bc colBase (.cr N t) k base toff),
      q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    rw [hown, upPairs_map] at hq
    rw [List.mem_map] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    have hjB : j < Bc := List.mem_range.mp hj
    have hmOn : (upCrIt (colBase + toff) (Bc + 1) base j).mOn = 1 := rfl
    rw [hmOn, Nat.mul_one]
    have h2 := (hpoint j hjB).2
    omega
  have hbitq : ∀ q ∈ upPairs E i c f (upOwnItems CR Bc colBase (.cr N t) k base toff),
      q.1 < 2 ^ E.W := by
    intro q hq
    rw [hown, upPairs_map] at hq
    rw [List.mem_map] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    have hjB : j < Bc := List.mem_range.mp hj
    rw [(hpoint j hjB).1]
    exact helemB j hjB
  have hltab : ∀ q, q < (CR.col N t c).card → tab (toff + (Bc + 1) * c + 1 + q) < 2 ^ E.W := by
    intro q hq
    have hmem : tab (toff + (Bc + 1) * c + 1 + q) ∈ CR.col N t c := by
      have himg := (hAt c hcN).2
      rw [← himg]
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_range.mpr (by rw [(hAt c hcN).1]; exact hq), rfl⟩
    have h2 := hcolrange hmem
    rw [Finset.mem_range] at h2
    omega
  have hinj : ∀ j j', j < (CR.col N t c).card → j' < (CR.col N t c).card →
      E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W
        = E.det ((Bc + 1) * c + (colBase + toff) + j' + 1) % 2 ^ E.W → j = j' := by
    intro j j' hj hj' he
    rw [det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
        (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j) hdet hcolBase,
      det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
        (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j') hdet hcolBase,
      Nat.mod_eq_of_lt (hltab j hj), Nat.mod_eq_of_lt (hltab j' hj')] at he
    exact upTabAt_inj CR Bc tab toff N t c hAt hcN j j' hj hj' he
  have hnd1 : (activeBits (upPairs E i c 1
      ((List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) base j)))).Nodup :=
    nodup_activeBits_ownCr CR E i c colBase N t base toff Bc hW hc (hperm 0 c) hbase
      (by omega) (by omega) (by omega) helemB hcard hcardB hinj
  have hnd : (activeBits (upPairs E i c f
      (upOwnItems CR Bc colBase (.cr N t) k base toff))).Nodup := by
    rw [hown, activeBits_upPairs_mul E i c f _ hf01]
    by_cases h : f = 1
    · rw [if_pos h]
      exact hnd1
    · rw [if_neg h]
      exact List.nodup_nil
  obtain ⟨h1, -, -⟩ :=
    upFold_own E i c f (upOwnItems CR Bc colBase (.cr N t) k base toff)
      hWpos hWlt hWw hc hf hfix hbit hwtf hmul hmul2 hwt hbitq hnd mem hmem a
  rw [h1, activeBits_ownCr_bitBlock (CR := CR) (E := E) (i := i) (N := N) (t := t) (c := c)
    (base := base) (toff := toff) (Bc := Bc) (f := f) (r := r) (k := k) (cnt := cnt) (W := W)
    (colBase := colBase) (items := items) (tab := tab)
    hW hc (hperm 0 c) hbase hdet hAt hcolrange hrows hBcW hcolBase hcN hbig hcardB helemB hf01]
theorem upRecOwnBits_eq_cr (CR : CRFamily) (sch : RowScheme) (t : ℕ) (child : Fin sch.ℓ → Node) (base c : ℕ) (leafSeed : Node.Seed (.cr sch.N t)) :
    bitBlock CR (.cr sch.N t) leafSeed {c} (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) =
      upRecOwnBits CR sch t child base c := by
  classical
  ext a
  rw [mem_bitBlock]
  unfold upRecOwnBits
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, ha⟩
    have hmem : p.val ∈ CR.sketch sch.N t {c} := by
      change (if p.val ∈ CR.sketch sch.N t {c} then (1 : ZMod 2) else 0) = 1 at hp
      by_cases hi : p.val ∈ CR.sketch sch.N t {c}
      · exact hi
      · simp [hi] at hp
    refine ⟨⟨p.val, p.isLt⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmem⟩
    · change base + ((∑ s : Fin sch.ℓ, synLen CR (child s)) + p.val) = a
      simpa only [Nat.add_assoc] using ha.symm
  · rintro ⟨q, hq, ha⟩
    have hmem := (Finset.mem_filter.mp hq).2
    refine ⟨⟨q.val, q.isLt⟩, ?_, ?_⟩
    · change (if q.val ∈ CR.sketch sch.N t {c} then (1 : ZMod 2) else 0) = 1
      rw [if_pos hmem]
    · change a = (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) + q.val
      simpa only [Nat.add_assoc] using ha.symm
theorem upPermAl_env (R : Node) (r₀ : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ) (k N : ℕ)
    (h : k < (hintSpec R).permSizes.length)
    (hlen : (hintSpec R).permSizes.get ⟨k, h⟩ = N) :
    PermAl (TableSpec.env (hintSpec R) W det r₀) k N (permNode R r₀ k N) := by
  subst hlen
  intro a ha
  simp only [TableSpec.env, permNode, dif_pos h, dif_pos rfl, dif_pos trivial, dif_pos ha]
theorem upCoefAl_env (P : HintParams) (R : Node) (r₀ : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (k N X Y : ℕ) (h : k < (hintSpec R).coeffShapes.length)
    (h2 : ((hintSpec R).coeffShapes.get ⟨k, h⟩).2 = 2) :
    CoefAl P (TableSpec.env (hintSpec R) W det r₀) k N X Y (coinsNode P R r₀ N X Y k) := by
  intro j s v
  have hval : ∀ (hq : (j.val * P.ell N X Y + s.val) * P.Nmax N X Y + v.val
      < ((hintSpec R).coeffShapes.get ⟨k, h⟩).1),
      (r₀.2 ⟨k, h⟩ ⟨_, hq⟩).val < 2 := by
    intro hq
    have hlt := (r₀.2 ⟨k, h⟩ ⟨_, hq⟩).isLt
    omega
  simp only [TableSpec.env, coinsNode, coeffAt]
  by_cases hq : (j.val * P.ell N X Y + s.val) * P.Nmax N X Y + v.val
      < ((hintSpec R).coeffShapes.get ⟨k, h⟩).1
  · simp only [dif_pos h, dif_pos hq]
    exact (zmod2_val_natCast (hval hq)).symm
  · simp only [dif_pos h, dif_neg hq, ZMod.val_zero]
theorem upAlignment_of_head (P : HintParams) (R T : Node)
    (rPublic : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ) (k N X Y : ℕ)
    (hhead : (schemeNodes R)[k]? = some T) (hN : T.N = N) :
    PermAl ((hintSpec R).env W det rPublic) k N (permNode R rPublic k N) ∧
      CoefAl P ((hintSpec R).env W det rPublic) k N X Y (coinsNode P R rPublic N X Y k) := by
  obtain ⟨hp, hpN⟩ := permSizes_get_of_block hhead
  obtain ⟨hc, hcS⟩ := coeffShapes_get_of_block hhead
  refine ⟨upPermAl_env R rPublic W det k N hp (hpN.trans hN),
    upCoefAl_env P R rPublic W det k N X Y hc ?_⟩
  rw [hcS]
  rfl
def UpTabFullTree (CR : CRFamily) (Bc : ℕ) (tab : ℕ → ℕ) : Node → ℕ → Prop
  | .store _, _ => True
  | .cr N t, toff => UpTabFullAt CR Bc tab N t toff
  | .direct sch t, toff => UpTabFullAt CR Bc tab sch.N t toff
  | .recursive sch t _ _ child, toff =>
      UpTabFullAt CR Bc tab sch.N t toff ∧
        ∀ s : Fin sch.ℓ, UpTabFullTree CR Bc tab (child s) (upKidOff Bc sch child toff s.val)
def UpCRColumns (CR : CRFamily) (Bc N t : ℕ) : Prop :=
  ∀ c, c < N → (CR.col N t c).card ≤ Bc ∧
    CR.col N t c ⊆ Finset.range (CR.rows N t)
def UpTreeStatic (CR : CRFamily) (Bc U : ℕ) : Node → Prop
  | .store N => N ≤ U
  | .cr N t => N ≤ U ∧ UpCRColumns CR Bc N t
  | .direct sch t => sch.N ≤ U ∧ 0 < sch.m ∧ UpCRColumns CR Bc sch.N t
  | .recursive sch t _ _ child => sch.N ≤ U ∧ 0 < sch.m ∧
      UpCRColumns CR Bc sch.N t ∧
      ∀ s, (child s).N = sch.m ∧ UpTreeStatic CR Bc U (child s)
theorem UpTreeStatic.universe {CR : CRFamily} {Bc U : ℕ} {T : Node}
    (h : UpTreeStatic CR Bc U T) : T.N ≤ U := by
  cases T with
  | store N => exact h
  | cr N t => exact h.1
  | direct sch t => exact h.1
  | recursive sch t Xs Ys child => exact h.1
theorem upEdgeData_of_alignment (P : HintParams) (E : RAMEnv) (i k N X Y c f : ℕ)
    (lr : Equiv.Perm (Fin N) × (Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2)) (s : Fin (P.ell N X Y))
    (hW : 1 < 2 ^ E.W) (hcN : c < N) (hNW : N ≤ 2 ^ E.W)
    (hm : 0 < P.rows X Y) (hmW : P.rows X Y ≤ 2 ^ E.W)
    (hPerm : PermAl E k N lr.1) (hCoef : CoefAl P E k N X Y lr.2)
    (hBit : E.perm k c % P.rows X Y * P.ell N X Y + s.val < 2 ^ E.W)
    (hIndex : (E.perm k c % P.rows X Y * P.ell N X Y + s.val) * P.Nmax N X Y +
      E.perm k c / P.rows X Y < 2 ^ E.W) :
    UpEdgeData E i k (P.scheme N X Y) lr s c f := by
  have hperm : E.perm k c < 2 ^ E.W := by
    rw [hPerm c hcN]
    exact lt_of_lt_of_le (lr.1 ⟨c, hcN⟩).isLt hNW
  let b := (P.scheme N X Y).code (rowOf0 (P.scheme N X Y) lr.1 hcN hm)
    (lr.2 (rowOf0 (P.scheme N X Y) lr.1 hcN hm))
    ((P.scheme N X Y).rowOf lr {c} (rowOf0 (P.scheme N X Y) lr.1 hcN hm)) s
  have hbW : b.val < 2 ^ E.W := lt_of_le_of_lt (zmod2_val_le_one b) hW
  have hqn : (E.perm k c % P.rows X Y * P.ell N X Y + s.val) * P.Nmax N X Y < 2 ^ E.W :=
    lt_of_le_of_lt (Nat.le_add_right _ _) hIndex
  have hcoin : upvCoin E i (upClimb k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) s)
      (⟨fun _ => 0, c, f⟩ : UpAbs) = if b = 1 then 1 else 0 := by
    have hsame : upvCoin E i (upClimb k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) s)
        (⟨fun _ => 0, c, f⟩ : UpAbs) =
      upvCoin E i (upColIt k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) 0 s)
        (⟨fun _ => 0, c, f⟩ : UpAbs) := rfl
    rw [hsame, upvCoin_colIt E i k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) 0 s
      (⟨fun _ => 0, c, f⟩ : UpAbs) hW hm hmW hperm hBit hqn hIndex,
      coefAl_code_singleton P E k N X Y c lr hcN hm hPerm hCoef s,
      Nat.mod_eq_of_lt hbW, zmod2_val_eq_ite]
  refine ⟨hm, hmW, hperm, hBit, ?_, ?_⟩
  · change upvCoin E i (upClimb k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) s)
      (⟨fun _ => 0, c, f⟩ : UpAbs) = 0 ∨
      upvCoin E i (upClimb k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) s)
        (⟨fun _ => 0, c, f⟩ : UpAbs) = 1
    rw [hcoin]
    by_cases hb : b = 1 <;> simp [hb]
  · change (P.scheme N X Y).column lr {c} s =
      if upvCoin E i (upClimb k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) s)
        (⟨fun _ => 0, c, f⟩ : UpAbs) = 1 then {E.perm k c % P.rows X Y} else ∅
    rw [hcoin]
    have hcol := column_singleton (sch := P.scheme N X Y) lr hcN hm s
    have hrow := rowOf_singleton_rowOf0 (sch := P.scheme N X Y) (lr := lr) hcN hm (rowOf0 (P.scheme N X Y) lr.1 hcN hm)
    rw [if_pos rfl] at hrow
    rw [← hrow] at hcol
    change (P.scheme N X Y).column lr {c} s = if b = 1 then _ else ∅ at hcol
    by_cases hb : b = 1
    · simp only [if_pos hb, if_pos rfl, if_pos trivial] at hcol ⊢
      rw [hPerm c hcN]
      exact hcol
    · simp only [if_neg hb, if_neg zero_ne_one] at hcol ⊢
      exact hcol
theorem upEdgeData_of_shape (P : HintParams) (E : RAMEnv) (i k N X Y c f : ℕ)
    (lr : Equiv.Perm (Fin N) × (Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2))
    (s : Fin (P.ell N X Y)) (hW : 1 < 2 ^ E.W) (hcN : c < N)
    (hm : 0 < P.rows X Y) (hNW : N ≤ 2 ^ E.W)
    (hPerm : PermAl E k N lr.1) (hCoef : CoefAl P E k N X Y lr.2)
    (hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ E.W) :
    UpEdgeData E i k (P.scheme N X Y) lr s c f := by
  have hpermN : E.perm k c < N := by
    rw [hPerm c hcN]
    exact (lr.1 ⟨c, hcN⟩).isLt
  have hpos : E.perm k c / P.rows X Y < P.Nmax N X Y :=
    div_lt_schemeNmax (P.scheme N X Y) hm hpermN
  have hEll : 1 ≤ P.ell N X Y := by unfold HintParams.ell; omega
  have hNmax : 1 ≤ P.Nmax N X Y :=
    (Nat.succ_le_succ (Nat.zero_le _)).trans (Nat.succ_le_of_lt hpos)
  have hMell : P.rows X Y ≤ P.rows X Y * P.ell N X Y := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (P.rows X Y) hEll
  have hMshape : P.rows X Y * P.ell N X Y ≤ P.rows X Y * P.ell N X Y * P.Nmax N X Y := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (P.rows X Y * P.ell N X Y) hNmax
  have hcol := up_mul_index_lt (P.rows X Y) (P.ell N X Y)
    (E.perm k c % P.rows X Y) s.val (Nat.mod_lt _ hm) s.isLt
  have hindex := up_mul_index_lt (P.rows X Y * P.ell N X Y) (P.Nmax N X Y)
    (E.perm k c % P.rows X Y * P.ell N X Y + s.val) (E.perm k c / P.rows X Y) hcol hpos
  exact upEdgeData_of_alignment P E i k N X Y c f lr s hW hcN hNW hm
    (hMell.trans (hMshape.trans hShape)) hPerm hCoef (hcol.trans_le (hMshape.trans hShape))
    (hindex.trans_le hShape)
theorem hintSpec_sizes_of_head (R T : Node) (k W : ℕ)
    (hhead : (schemeNodes R)[k]? = some T) (hFits : (hintSpec R).Fits W) :
    T.N ≤ 2 ^ W ∧ (nodeCoins T).1 ≤ 2 ^ W := by
  obtain ⟨hp, hpN⟩ := permSizes_get_of_block hhead
  obtain ⟨hc, hcS⟩ := coeffShapes_get_of_block hhead
  have hN := hFits.2.2.1 ((hintSpec R).permSizes.get ⟨k, hp⟩) (List.get_mem _ _)
  have hS := hFits.2.2.2 ((hintSpec R).coeffShapes.get ⟨k, hc⟩) (List.get_mem _ _)
  rw [hpN] at hN
  rw [hcS] at hS
  exact ⟨hN, hS.1⟩
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upLocal_cr_of_table (CR : CRFamily) (spec : TableSpec) (W cnt Bc colBase : ℕ)
    (items : List UpIt) (tab : ℕ → ℕ) (rPublic : spec.Seed) (i N t k base toff : ℕ)
    (rTree : Node.Seed (.cr N t))
    (hW : 1 < 2 ^ W) (hWpos : 0 < W) (hFits : spec.Fits W) (hNW : N ≤ 2 ^ W)
    (hCol : 4 < colBase) (hEnd : colBase + toff + N * (Bc + 1) < 2 ^ W)
    (hBaseRows : base + CR.rows N t < 2 ^ W)
    (hFull : UpTabFullAt CR Bc tab N t toff)
    (hCard : ∀ c, c < N → (CR.col N t c).card ≤ Bc)
    (hRange : ∀ c, c < N → CR.col N t c ⊆ Finset.range (CR.rows N t)) :
    UpLocalBitsCorrect CR (spec.env W (upDet cnt W colBase items tab) rPublic)
      i Bc colBase (.cr N t) rTree k base toff := by
  let E := spec.env W (upDet cnt W colBase items tab) rPublic
  change UpLocalBitsCorrect CR E i Bc colBase (.cr N t) rTree k base toff
  intro c f hcN hc hf hf01 mem hm a
  change c < N at hcN
  have hrow := Nat.mul_le_mul_right (Bc + 1) (Nat.succ_le_of_lt hcN)
  have hBig : (Bc + 1) * c + (colBase + toff) + Bc + 1 < 2 ^ W := by
    calc
      (Bc + 1) * c + (colBase + toff) + Bc + 1 = colBase + toff + (c + 1) * (Bc + 1) := by ring
      _ ≤ colBase + toff + N * (Bc + 1) := Nat.add_le_add_left hrow _
      _ < 2 ^ W := hEnd
  have hBase : base < 2 ^ W := lt_of_le_of_lt (Nat.le_add_right _ _) hBaseRows
  have hRows : CR.rows N t ≤ 2 ^ W := by omega
  have hBc : Bc < 2 ^ W := by omega
  have hAt := UpTabFullAt.to_set CR Bc tab toff N t hFull hCard
  have hWW : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W := upDet_width_read cnt W colBase items tab hW
  have helem : ∀ j, j < Bc →
      base + E.det ((Bc + 1) * c + (colBase + toff) + j + 1) % 2 ^ E.W < 2 ^ E.W := by
    intro j hj
    rw [det_eq_tab (E := E) (cnt := cnt) (W := W) (colBase := colBase) (items := items)
      (tab := tab) (Bc := Bc) (toff := toff) (c := c) (j := j) rfl hCol]
    exact UpTabFullAt.payload_bounds CR Bc tab toff N t base W hFull hRange hBaseRows c hcN j hj
  have hh := upFold_node_cr CR E i N t base c f a rTree k toff Bc colBase 0 cnt W items tab
    hW hWpos (Nat.lt_two_pow_self (n := W)) hWW hc hf hf01
    (env_perm_lt_word spec W _ rPublic hFits) hBase rfl hAt (hRange c hcN)
    hRows hBc hCol hcN hBig (hCard c hcN) helem mem hm
  simpa only [upKids, List.append_nil, upNodeLocalBits] using hh
theorem upLocal_store_of_table (CR : CRFamily) (spec : TableSpec) (W cnt Bc colBase : ℕ)
    (items : List UpIt) (tab : ℕ → ℕ) (rPublic : spec.Seed) (i N k base toff : ℕ)
    (rTree : Node.Seed (.store N)) (hW : 1 < 2 ^ W) (hWpos : 0 < W)
    (hN : 0 < N) (hBaseN : base + N < 2 ^ W) :
    UpLocalBitsCorrect CR (spec.env W (upDet cnt W colBase items tab) rPublic)
      i Bc colBase (.store N) rTree k base toff := by
  let E := spec.env W (upDet cnt W colBase items tab) rPublic
  change UpLocalBitsCorrect CR E i Bc colBase (.store N) rTree k base toff
  intro c f hcN hc hf hf01 mem hm a
  have hNW : N ≤ 2 ^ W := by omega
  have hBase : base < 2 ^ W := by omega
  have hBit : base + c % N < 2 ^ W := (Nat.add_lt_add_left (Nat.mod_lt c hN) base).trans hBaseN
  have hWW : E.det (1 % 2 ^ E.W) % 2 ^ E.W = E.W := upDet_width_read cnt W colBase items tab hW
  have hh := upFold_node_store CR E i N base c f a rTree k toff Bc colBase 0
    hW hWpos (Nat.lt_two_pow_self (n := W)) hWW hN hNW hc hcN hf hf01 hBase hBit mem hm
  simpa only [upKids, List.append_nil, upNodeLocalBits] using hh
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upLocal_recursive_of_table (CR : CRFamily) (spec : TableSpec) (W cnt Bc colBase : ℕ)
    (items : List UpIt) (tab : ℕ → ℕ) (rPublic : spec.Seed) (i k base toff : ℕ)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)
    (rTree : Node.Seed (.recursive sch t Xs Ys child))
    (hW : 1 < 2 ^ W) (hWpos : 0 < W) (hFits : spec.Fits W) (hNW : sch.N ≤ 2 ^ W)
    (hCol : 4 < colBase) (hEnd : colBase + toff + sch.N * (Bc + 1) < 2 ^ W)
    (hAll : base + (∑ s : Fin sch.ℓ, synLen CR (child s)) + CR.rows sch.N t < 2 ^ W)
    (hFull : UpTabFullAt CR Bc tab sch.N t toff)
    (hCard : ∀ c, c < sch.N → (CR.col sch.N t c).card ≤ Bc)
    (hRange : ∀ c, c < sch.N → CR.col sch.N t c ⊆ Finset.range (CR.rows sch.N t)) :
    UpLocalBitsCorrect CR (spec.env W (upDet cnt W colBase items tab) rPublic)
      i Bc colBase (.recursive sch t Xs Ys child) rTree k base toff := by
  let E := spec.env W (upDet cnt W colBase items tab) rPublic
  let leafSeed : Node.Seed (.cr sch.N t) := ()
  have hCR := upLocal_cr_of_table CR spec W cnt Bc colBase items tab rPublic i sch.N t k
    (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) toff leafSeed
    hW hWpos hFits hNW hCol hEnd hAll hFull hCard hRange
  intro c f hcN hc hf hf01 mem hm a
  have hh := hCR c f hcN hc hf hf01 mem hm a
  change (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.cr sch.N t) k
      (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) toff)).mem a =
    mem a ^^^ packSel W (if f = 1 then bitBlock CR (.cr sch.N t) leafSeed {c}
      (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) else ∅) a at hh
  rw [upRecOwnBits_eq_cr CR sch t child base c leafSeed] at hh
  change (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff)).mem a =
    mem a ^^^ packSel W (if f = 1 then upRecOwnBits CR sch t child base c else ∅) a
  exact hh
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upLocalTree_of_tables (CR : CRFamily) (P : HintParams) (R : Node)
    (W cnt Bc colBase U : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (rPublic : (hintSpec R).Seed) (i : ℕ)
    (hW : 1 < 2 ^ W) (hWpos : 0 < W) (hFits : (hintSpec R).Fits W)
    (hCol : 4 < colBase) (hU : U ≤ 2 ^ W)
    (T : Node) (hT : IsSchemeTree P T) :
    ∀ k base toff, BlockOf R k (schemeNodes T) → UpTreeStatic CR Bc U T →
      UpTabFullTree CR Bc tab T toff →
      colBase + toff + upTabLen Bc T < 2 ^ W → base + synLen CR T < 2 ^ W →
      UpLocalTree CR ((hintSpec R).env W (upDet cnt W colBase items tab) rPublic)
        i Bc colBase T (hintKappaAux P R rPublic T hT k) k base toff := by
  induction hT with
  | store N =>
      intro k base toff hb hStatic hFull hEnd hBits
      by_cases hN : 0 < N
      · exact upLocal_store_of_table CR (hintSpec R) W cnt Bc colBase items tab rPublic
          i N k base toff () hW hWpos hN hBits
      · intro c f hcN
        change c < N at hcN
        omega
  | cr N t =>
      intro k base toff hb hStatic hFull hEnd hBits
      exact upLocal_cr_of_table CR (hintSpec R) W cnt Bc colBase items tab rPublic i N t k
        base toff () hW hWpos hFits (hStatic.1.trans hU) hCol hEnd hBits hFull
        (fun c hc => (hStatic.2 c hc).1) (fun c hc => (hStatic.2 c hc).2)
  | direct N X Y t =>
      intro k base toff hb hStatic hFull hEnd hBits
      have hhead := BlockOf_head hb
      have hSizes := hintSpec_sizes_of_head R _ k W hhead hFits
      have hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ W := hSizes.2
      have hAlign := upAlignment_of_head P R _ rPublic W (upDet cnt W colBase items tab)
        k N X Y hhead rfl
      exact upLocal_direct_of_table CR P (hintSpec R) W cnt Bc colBase items tab rPublic
        i N X Y t k base toff (permNode R rPublic k N, coinsNode P R rPublic N X Y k)
        hW hWpos hFits hStatic.2.1 hCol hAlign.1 hAlign.2 hShape hEnd
        (by simpa only [synLen, HintParams.scheme, Nat.add_assoc] using hBits) hFull
        (fun c hc => (hStatic.2.2 c hc).1) (fun c hc => (hStatic.2.2 c hc).2)
  | recursive N X Y t Xs Ys child hchild ih =>
      intro k base toff hb hStatic hFull hEnd hBits
      have hhead := BlockOf_head hb
      have hSizes := hintSpec_sizes_of_head R _ k W hhead hFits
      have hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ W := hSizes.2
      have hAlign := upAlignment_of_head P R _ rPublic W (upDet cnt W colBase items tab)
        k N X Y hhead rfl
      have hOwnLen : N * (Bc + 1) ≤ upTabLen Bc
          (.recursive (P.scheme N X Y) t Xs Ys child) := by
        simpa only [upOwn, HintParams.scheme] using
          (upOwn_le_tabLen Bc (.recursive (P.scheme N X Y) t Xs Ys child))
      have hOwnEnd : colBase + toff + N * (Bc + 1) < 2 ^ W := by omega
      refine ⟨?_, fun s => (hStatic.2.2.2 s).1, ?_, ?_⟩
      · exact upLocal_recursive_of_table CR (hintSpec R) W cnt Bc colBase items tab rPublic
          i k base toff (P.scheme N X Y) t Xs Ys child
          (hintKappaAux P R rPublic _ (IsSchemeTree.recursive N X Y t Xs Ys child hchild) k)
          hW hWpos hFits (hStatic.1.trans hU) hCol hOwnEnd
          (by simpa only [synLen, HintParams.scheme, Nat.add_assoc] using hBits) hFull.1
          (fun c hc => (hStatic.2.2.1 c hc).1) (fun c hc => (hStatic.2.2.1 c hc).2)
      · intro c f hcN hc hf hf01 s
        exact upEdgeData_of_shape P _ i k N X Y c f
          (permNode R rPublic k N, coinsNode P R rPublic N X Y k) s hW hcN
          hStatic.2.1 (hStatic.1.trans hU) hAlign.1 hAlign.2 hShape
      · intro s
        apply ih s _ _ _ (BlockOf_child hb s) (hStatic.2.2.2 s).2 (hFull.2 s)
        · have hTop := upKidOff_le_top Bc (P.scheme N X Y) child toff s.val s.isLt
          have hTop' : upKidOff Bc (P.scheme N X Y) child toff s.val + upTabLen Bc (child s) ≤
              toff + upTabLen Bc (.recursive (P.scheme N X Y) t Xs Ys child) := hTop
          change colBase + upKidOff Bc (P.scheme N X Y) child toff s.val + upTabLen Bc (child s) < 2 ^ W
          omega
        · have hSum := take_sum_add_getElem_le
            (List.ofFn fun j : Fin (P.scheme N X Y).ℓ => synLen CR (child j)) s.val
            (synLen CR (child s)) (getElem?_ofFn' _ s)
          rw [List.sum_ofFn] at hSum
          have hB : base + (∑ s, synLen CR (child s)) + CR.rows N t < 2 ^ W := by
            simpa only [synLen, HintParams.scheme, Nat.add_assoc] using hBits
          omega
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
def UpEllOK (Bℓ : ℕ) : Node → Prop
  | .store _ => True
  | .cr _ _ => True
  | .direct sch _ => sch.ℓ ≤ Bℓ
  | .recursive sch _ _ _ child => sch.ℓ ≤ Bℓ ∧ ∀ s, UpEllOK Bℓ (child s)
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upTabLen_le_static (CR : CRFamily) (Bc U : ℕ) :
    ∀ T, UpTreeStatic CR Bc U T → upTabLen Bc T ≤ T.nodeCount * U * (Bc + 1) := by
  intro T
  induction T with
  | store N => intro h; simp only [upTabLen, Node.nodeCount]; omega
  | cr N t =>
      intro h
      simpa only [upTabLen, Node.nodeCount, Nat.one_mul] using Nat.mul_le_mul_right (Bc + 1) h.1
  | direct sch t =>
      intro h
      simpa only [upTabLen, Node.nodeCount, Nat.one_mul] using Nat.mul_le_mul_right (Bc + 1) h.1
  | recursive sch t Xs Ys child ih =>
      intro h
      have hs : (∑ s : Fin sch.ℓ, upTabLen Bc (child s)) ≤
          ∑ s : Fin sch.ℓ, (child s).nodeCount * U * (Bc + 1) := by
        apply Finset.sum_le_sum
        intro s _
        exact ih s (h.2.2.2 s).2
      calc
        upTabLen Bc (.recursive sch t Xs Ys child) =
            sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s) := rfl
        _ ≤ U * (Bc + 1) + ∑ s : Fin sch.ℓ, (child s).nodeCount * U * (Bc + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right (Bc + 1) h.1) hs
        _ = (Node.recursive sch t Xs Ys child).nodeCount * U * (Bc + 1) := by
          simp only [Node.nodeCount, Finset.sum_mul, Nat.add_mul, Nat.one_mul]
theorem schemeNodes_length_rec (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) :
    (schemeNodes (.recursive sch t Xs Ys child)).length =
      1 + ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length := by
  simp only [schemeNodes, List.length_append, List.length_singleton,
    flatten_length_eq_sum, List.sum_ofFn]
theorem up_nodeCount_le_schemeNodes (B : ℕ) : ∀ T, UpEllOK B T →
    T.nodeCount ≤ 1 + B * (schemeNodes T).length := by
  intro T
  induction T with
  | store N => intro h; simp only [Node.nodeCount, schemeNodes, List.length_nil, Nat.mul_zero, Nat.add_zero]; exact le_rfl
  | cr N t => intro h; simp only [Node.nodeCount, schemeNodes, List.length_nil, Nat.mul_zero, Nat.add_zero]; exact le_rfl
  | direct sch t => intro h; simp only [Node.nodeCount, schemeNodes, List.length_singleton, Nat.mul_one]; omega
  | recursive sch t Xs Ys child ih =>
      intro h
      have hEll : sch.ℓ ≤ B := h.1
      have hs : (∑ s : Fin sch.ℓ, (child s).nodeCount) ≤
          ∑ s : Fin sch.ℓ, (1 + B * (schemeNodes (child s)).length) := by
        apply Finset.sum_le_sum
        intro s _
        exact ih s (h.2 s)
      calc
        (Node.recursive sch t Xs Ys child).nodeCount =
            1 + ∑ s : Fin sch.ℓ, (child s).nodeCount := rfl
        _ ≤ 1 + ∑ s : Fin sch.ℓ, (1 + B * (schemeNodes (child s)).length) := Nat.add_le_add_left hs 1
        _ = 1 + (sch.ℓ + B * ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
        _ ≤ 1 + (B + B * ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) := by omega
        _ = 1 + B * (1 + ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) := by ring
        _ = 1 + B * (schemeNodes (.recursive sch t Xs Ys child)).length := by rw [schemeNodes_length_rec]
theorem up_depth_le_schemeNodes : ∀ T : Node, T.depth ≤ (schemeNodes T).length + 1 := by
  intro T
  induction T with
  | store N => simp [Node.depth, schemeNodes]
  | cr N t => simp [Node.depth, schemeNodes]
  | direct sch t => simp [Node.depth, schemeNodes]
  | recursive sch t Xs Ys child ih =>
      have hs : Finset.univ.sup (fun s : Fin sch.ℓ => (child s).depth) ≤
          (∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) + 1 := by
        apply Finset.sup_le
        intro s _
        have hSi : (schemeNodes (child s)).length ≤
            ∑ j : Fin sch.ℓ, (schemeNodes (child j)).length :=
          Finset.single_le_sum (fun (j : Fin sch.ℓ) _ => Nat.zero_le (schemeNodes (child j)).length) (Finset.mem_univ s)
        exact (ih s).trans (Nat.add_le_add_right hSi 1)
      rw [schemeNodes_length_rec]
      change 1 + Finset.univ.sup (fun s : Fin sch.ℓ => (child s).depth) ≤ _
      omega
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def UpDimsBound (Q : ℕ) : Node → Prop
  | .store N => N ≤ Q
  | .cr N _ => N ≤ Q
  | .direct sch _ => sch.N ≤ Q ∧ sch.m ≤ Q ∧ sch.ℓ ≤ Q ∧ schemeNmax sch ≤ Q
  | .recursive sch _ _ _ child =>
      sch.N ≤ Q ∧ sch.m ≤ Q ∧ sch.ℓ ≤ Q ∧ schemeNmax sch ≤ Q ∧
        ∀ s, UpDimsBound Q (child s)
theorem UpDimsBound.universe {Q : ℕ} {T : Node} (h : UpDimsBound Q T) : T.N ≤ Q := by
  cases T with
  | store N => exact h
  | cr N t => exact h
  | direct sch t => exact h.1
  | recursive sch t Xs Ys child => exact h.1
theorem up_dimensions_of_shape (P : HintParams) (N X Y Q : ℕ)
    (hN : 0 < N) (hm : 0 < P.rows X Y)
    (hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ Q) :
    P.rows X Y ≤ Q ∧ P.ell N X Y ≤ Q ∧ P.Nmax N X Y ≤ Q := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hmreal : (0 : ℝ) < P.rows X Y := by exact_mod_cast hm
  have hdiv : (0 : ℝ) < (N : ℝ) / (P.rows X Y : ℝ) := div_pos hNreal hmreal
  have hVreal : (0 : ℝ) < (P.Nmax N X Y : ℕ) := hdiv.trans_le (Nat.le_ceil _)
  have hV : 1 ≤ P.Nmax N X Y := by exact_mod_cast hVreal
  have hL : 1 ≤ P.ell N X Y := by unfold HintParams.ell; omega
  have hM : 1 ≤ P.rows X Y := by omega
  have hML1 : 1 ≤ P.rows X Y * P.ell N X Y := Nat.mul_pos hm (by omega)
  have hML : P.rows X Y * P.ell N X Y ≤ P.rows X Y * P.ell N X Y * P.Nmax N X Y := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (P.rows X Y * P.ell N X Y) hV
  have hmML : P.rows X Y ≤ P.rows X Y * P.ell N X Y := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (P.rows X Y) hL
  have hlML : P.ell N X Y ≤ P.rows X Y * P.ell N X Y := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P.ell N X Y) hM
  have hvShape : P.Nmax N X Y ≤ P.rows X Y * P.ell N X Y * P.Nmax N X Y := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P.Nmax N X Y) hML1
  exact ⟨hmML.trans (hML.trans hShape), hlML.trans (hML.trans hShape), hvShape.trans hShape⟩
theorem upDims_of_tables (CR : CRFamily) (P : HintParams) (R : Node) (W Bc U : ℕ)
    (hFits : (hintSpec R).Fits W) (hU : U ≤ 2 ^ W) (T : Node) (hT : IsSchemeTree P T) :
    ∀ k, BlockOf R k (schemeNodes T) → UpTreeStatic CR Bc U T →
      0 < T.N → UpDimsBound (2 ^ W) T := by
  induction hT with
  | store N => intro k hb hs hN; exact hs.trans hU
  | cr N t => intro k hb hs hN; exact hs.1.trans hU
  | direct N X Y t =>
      intro k hb hs hN
      have hhead := BlockOf_head hb
      have hSize := hintSpec_sizes_of_head R _ k W hhead hFits
      have hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ W := hSize.2
      obtain ⟨hm, hl, hv⟩ := up_dimensions_of_shape P N X Y (2 ^ W) hN hs.2.1 hShape
      exact ⟨hs.1.trans hU, hm, hl, hv⟩
  | recursive N X Y t Xs Ys child hchild ih =>
      intro k hb hs hN
      have hhead := BlockOf_head hb
      have hSize := hintSpec_sizes_of_head R _ k W hhead hFits
      have hShape : P.rows X Y * P.ell N X Y * P.Nmax N X Y ≤ 2 ^ W := hSize.2
      obtain ⟨hm, hl, hv⟩ := up_dimensions_of_shape P N X Y (2 ^ W) hN hs.2.1 hShape
      refine ⟨hs.1.trans hU, hm, hl, hv, ?_⟩
      intro s
      apply ih s _ (BlockOf_child hb s) (hs.2.2.2 s).2
      rw [(hs.2.2.2 s).1]
      exact hs.2.1
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
theorem upDet_item (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) (k f : ℕ)
    (hk : k < items.length) (hf : f < 16) (hcol : 8 + 16 * items.length ≤ colBase) :
    upDet cnt W colBase items tab (8 + (16 * k + f)) = (items.getD k upItZero).fld f := by
  have h0 : 8 + (16 * k + f) ≠ 0 := by omega
  have h1 : 8 + (16 * k + f) ≠ 1 := by omega
  have h2 : 8 + (16 * k + f) ≠ 2 := by omega
  have h3 : 8 + (16 * k + f) ≠ 3 := by omega
  have hc : ¬ colBase ≤ 8 + (16 * k + f) := by omega
  have e1 : 8 + (16 * k + f) - 8 = 16 * k + f := Nat.add_sub_cancel_left _ _
  have e2 : (16 * k + f) / 16 = k := by
    rw [Nat.mul_add_div (by norm_num : 0 < 16), Nat.div_eq_of_lt hf, Nat.add_zero]
  have e3 : (16 * k + f) % 16 = f := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  unfold upDet
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg hc, e1, e2, e3]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def UpFldBound (F : ℕ) (it : UpIt) : Prop := ∀ t, t < 16 → it.fld t ≤ F
theorem upFld_reset (F N : ℕ) (hF : 3 ≤ F) (h : N ≤ F) :
    UpFldBound F (upReset N) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upReset] <;> omega
theorem upFld_climb (F k m ell nmax s : ℕ) (hF : 3 ≤ F) (h : k ≤ F ∧ m ≤ F ∧ ell ≤ F ∧ nmax ≤ F ∧ s ≤ F) :
    UpFldBound F (upClimb k m ell nmax s) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upClimb] <;> omega
theorem upFld_store (F N base : ℕ) (hF : 3 ≤ F) (h : N ≤ F ∧ base ≤ F) :
    UpFldBound F (upStoreIt N base) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upStoreIt] <;> omega
theorem upFld_col (F k m ell nmax base s : ℕ) (hF : 3 ≤ F) (h : k ≤ F ∧ m ≤ F ∧ ell ≤ F ∧ nmax ≤ F ∧ base ≤ F ∧ s ≤ F) :
    UpFldBound F (upColIt k m ell nmax base s) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upColIt] <;> omega
theorem upFld_cr (F cidx stride base j : ℕ) (hF : 3 ≤ F) (h : cidx ≤ F ∧ stride ≤ F ∧ base ≤ F ∧ j ≤ F) :
    UpFldBound F (upCrIt cidx stride base j) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upCrIt] <;> omega
theorem upFld_save (F sav : ℕ) (hF : 3 ≤ F) (h : sav ≤ F) :
    UpFldBound F (upSave sav) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upSave] <;> omega
theorem upFld_restore (F sav : ℕ) (hF : 3 ≤ F) (h : sav ≤ F) :
    UpFldBound F (upRestore sav) := by
  intro t ht
  interval_cases t <;> simp only [UpIt.fld, upRestore] <;> omega
theorem upHead_fields_le (F N k : ℕ) (hF : 3 ≤ F) (hN : N ≤ F) :
    ∀ it ∈ upHead N k, UpFldBound F it := by
  intro it hi
  unfold upHead at hi
  split_ifs at hi with hk
  · rw [List.mem_singleton] at hi
    subst it
    exact upFld_reset F N hF hN
  · simp at hi
theorem upOwnItems_fields_le (CR : CRFamily) (Bc colBase F : ℕ) (T : Node)
    (k base toff : ℕ) (hF : 3 ≤ F) (hBc : Bc + 1 ≤ F) (hDims : UpDimsBound F T)
    (hK : k ≤ F) (hBits : base + synLen CR T ≤ F)
    (hTab : colBase + toff + upTabLen Bc T ≤ F) :
    ∀ it ∈ upOwnItems CR Bc colBase T k base toff, UpFldBound F it := by
  cases T with
  | store N =>
      intro it hi
      simp only [upOwnItems, List.mem_singleton] at hi
      subst it
      exact upFld_store F N base hF ⟨hDims, by omega⟩
  | cr N t =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hj' := List.mem_range.mp hj
      exact upFld_cr F (colBase + toff) (Bc + 1) base j hF
        ⟨by omega, hBc, by omega, by omega⟩
  | direct sch t =>
      intro it hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
        have hs' := List.mem_range.mp hs
        exact upFld_col F k sch.m sch.ℓ (schemeNmax sch) base s hF
          ⟨hK, hDims.2.1, hDims.2.2.1, hDims.2.2.2, by omega, (Nat.le_of_lt hs').trans hDims.2.2.1⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        have hj' := List.mem_range.mp hj
        have hB : base + (sch.m * sch.ℓ + CR.rows sch.N t) ≤ F := hBits
        exact upFld_cr F (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j hF
          ⟨by omega, hBc, by omega, by omega⟩
  | recursive sch t Xs Ys child =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hj' := List.mem_range.mp hj
      have hB : base + ((∑ s, synLen CR (child s)) + CR.rows sch.N t) ≤ F := hBits
      exact upFld_cr F (colBase + toff) (Bc + 1) (base + ∑ s, synLen CR (child s)) j hF
        ⟨by omega, hBc, by omega, by omega⟩
theorem upSched_fields_le_of_parts (CR : CRFamily) (Bc colBase F : ℕ) (T : Node)
    (k base toff sav : ℕ) (path : List UpIt) (hF : 3 ≤ F) (hN : T.N ≤ F)
    (hPath : ∀ it ∈ path, UpFldBound F it)
    (hOwn : ∀ it ∈ upOwnItems CR Bc colBase T k base toff, UpFldBound F it)
    (hKids : ∀ it ∈ upKids CR Bc colBase T k base toff sav path, UpFldBound F it) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, UpFldBound F it := by
  intro it hi
  rw [upSched_decomp] at hi
  rcases List.mem_append.mp hi with hh | ht
  · exact upHead_fields_le F T.N k hF hN it hh
  · rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with hp | ho
      · exact hPath it hp
      · exact hOwn it ho
    · exact hKids it ht
theorem upSched_fields_le (CR : CRFamily) (Bc colBase F : ℕ) (hF : 3 ≤ F) (hBc : Bc + 1 ≤ F)
    (T : Node) : ∀ k base toff sav path,
    UpDimsBound F T → k + (schemeNodes T).length ≤ F →
    base + synLen CR T ≤ F → colBase + toff + upTabLen Bc T ≤ F → sav ≤ F →
    (∀ it ∈ path, UpFldBound F it) →
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, UpFldBound F it := by
  induction T with
  | store N =>
      intro k base toff sav path hDims hK hBits hTab hSav hPath
      apply upSched_fields_le_of_parts CR Bc colBase F _ k base toff sav path hF
        hDims.universe hPath
        (upOwnItems_fields_le CR Bc colBase F _ k base toff hF hBc hDims (by omega) hBits hTab)
      intro it hi
      simp [upKids] at hi
  | cr N t =>
      intro k base toff sav path hDims hK hBits hTab hSav hPath
      apply upSched_fields_le_of_parts CR Bc colBase F _ k base toff sav path hF
        hDims.universe hPath
        (upOwnItems_fields_le CR Bc colBase F _ k base toff hF hBc hDims (by omega) hBits hTab)
      intro it hi
      simp [upKids] at hi
  | direct sch t =>
      intro k base toff sav path hDims hK hBits hTab hSav hPath
      apply upSched_fields_le_of_parts CR Bc colBase F _ k base toff sav path hF
        hDims.universe hPath
        (upOwnItems_fields_le CR Bc colBase F _ k base toff hF hBc hDims (by omega) hBits hTab)
      intro it hi
      simp [upKids] at hi
  | recursive sch t Xs Ys child ih =>
      intro k base toff sav path hDims hK hBits hTab hSav hPath
      apply upSched_fields_le_of_parts CR Bc colBase F _ k base toff sav path hF
        hDims.universe hPath
        (upOwnItems_fields_le CR Bc colBase F _ k base toff hF hBc hDims (by omega) hBits hTab)
      intro it hi
      unfold upKids at hi
      obtain ⟨L, hL, hit⟩ := List.mem_flatten.mp hi
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hL
      rcases List.mem_cons.mp hit with he | hrest
      · subst it
        unfold upSiblingEntry
        split_ifs
        · exact upFld_save F sav hF hSav
        · exact upFld_restore F sav hF hSav
      · have hSum := take_sum_add_getElem_le
          (List.ofFn fun j : Fin sch.ℓ => (schemeNodes (child j)).length) s.val
          (schemeNodes (child s)).length (getElem?_ofFn' _ s)
        rw [List.sum_ofFn] at hSum
        have hKidK : k + 1 + ((List.ofFn fun j : Fin sch.ℓ =>
            (schemeNodes (child j)).length).take s.val).sum + (schemeNodes (child s)).length ≤ F := by
          rw [schemeNodes_length_rec] at hK
          omega
        have hSumBits := take_sum_add_getElem_le
          (List.ofFn fun j : Fin sch.ℓ => synLen CR (child j)) s.val
          (synLen CR (child s)) (getElem?_ofFn' _ s)
        rw [List.sum_ofFn] at hSumBits
        have hKidBits : base + ((List.ofFn fun j : Fin sch.ℓ =>
            synLen CR (child j)).take s.val).sum + synLen CR (child s) ≤ F := by
          change base + ((∑ j, synLen CR (child j)) + CR.rows sch.N t) ≤ F at hBits
          omega
        have hTop := upKidOff_le_top Bc sch child toff s.val s.isLt
        have hTop' : upKidOff Bc sch child toff s.val + upTabLen Bc (child s) ≤
            toff + (sch.N * (Bc + 1) + ∑ j, upTabLen Bc (child j)) := hTop
        have hKidTab : colBase + upKidOff Bc sch child toff s.val + upTabLen Bc (child s) ≤ F := by
          change colBase + toff + (sch.N * (Bc + 1) + ∑ j, upTabLen Bc (child j)) ≤ F at hTab
          omega
        exact ih s _ _ _ _ _ (hDims.2.2.2.2 s) hKidK hKidBits hKidTab
          ((Nat.sub_le _ _).trans hSav)
          (by
            intro u hu
            rw [List.mem_singleton] at hu
            subst u
            exact upFld_climb F k sch.m sch.ℓ (schemeNmax sch) s.val hF
              ⟨by omega, hDims.2.1, hDims.2.2.1, hDims.2.2.2.1,
                (Nat.le_of_lt s.isLt).trans hDims.2.2.1⟩) it hrest
theorem upDet_fields_from_le (cnt W colBase F : ℕ) (items : List UpIt) (tab : ℕ → ℕ)
    (hF : F < 2 ^ W) (hCol : 8 + 16 * items.length ≤ colBase)
    (hFields : ∀ it ∈ items, UpFldBound F it) :
    ∀ j (hj : j < items.length), ∀ t, t < 16 →
      upDet cnt W colBase items tab (8 + 16 * j + t) % 2 ^ W = (items[j]).fld t := by
  intro j hj t ht
  have hItem := hFields (items[j]) (List.getElem_mem hj) t ht
  have hRead := upDet_item cnt W colBase items tab j t hj ht hCol
  rw [← Nat.add_assoc] at hRead
  rw [hRead, List.getD_eq_getElem _ _ hj, Nat.mod_eq_of_lt (hItem.trans_lt hF)]
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
lemma one_le_depth (T : Node) : 1 ≤ T.depth := by
  induction T with
  | store N => simp [Node.depth]
  | cr N t => simp [Node.depth]
  | direct sch t => simp [Node.depth]
  | recursive sch t Xs Ys child ih => simp only [Node.depth]; omega
@[simp] theorem upDet_zero (cnt W colBase : ℕ) (items : List UpIt) (tab : ℕ → ℕ) :
    upDet cnt W colBase items tab 0 = cnt := by unfold upDet; simp
theorem upHead_length_le (N k : ℕ) : (upHead N k).length ≤ 1 := by
  by_cases h : k = 0 <;> simp [upHead, h]
def upRest (Bc : ℕ) : Node → ℕ
  | .store _ => 1
  | .cr _ _ => Bc
  | .direct sch _ => sch.ℓ + Bc
  | .recursive sch _ _ _ child => Bc + ∑ s : Fin sch.ℓ, (2 + upRest Bc (child s))
def upCnt (Bc : ℕ) : Node → ℕ → ℕ
  | .store _, p => 1 + p + 1
  | .cr _ _, p => 1 + p + Bc
  | .direct sch _, p => 1 + p + sch.ℓ + Bc
  | .recursive sch _ _ _ child, p => 1 + p + Bc + sch.ℓ + ∑ s : Fin sch.ℓ, upCnt Bc (child s) (p + 1)
theorem length_flatten_ofFn {α : Type} :
    ∀ (n : ℕ) (f : Fin n → List α), (List.ofFn f).flatten.length = ∑ i, (f i).length
  | 0, _ => by simp
  | n + 1, f => by
      rw [List.ofFn_succ]
      simp only [List.flatten_cons, List.length_append, Fin.sum_univ_succ]
      rw [length_flatten_ofFn n (fun i => f i.succ)]
theorem upSched_length (CR : CRFamily) (Bc colBase : ℕ) (T : Node) :
    ∀ (k base toff sav : ℕ) (path : List UpIt),
      (upSched CR Bc colBase T k base toff sav path).length
        = (upHead (Node.N T) k).length + path.length + upRest Bc T := by
  induction T with
  | store N =>
      intro k base toff sav path
      simp only [upSched, upRest, Node.N, List.length_append, List.length_singleton,
        List.length_nil]
      omega
  | cr N t =>
      intro k base toff sav path
      simp only [upSched, upRest, Node.N, List.length_append, List.length_map,
        List.length_range, List.length_nil]
      omega
  | direct sch t =>
      intro k base toff sav path
      simp only [upSched, upRest, Node.N, List.length_append, List.length_map,
        List.length_range, List.length_nil]
      omega
  | recursive sch t Xs Ys child ih =>
      intro k base toff sav path
      have hstep : ∀ s : Fin sch.ℓ,
          (upSiblingEntry sav s.val :: upSched CR Bc colBase (child s)
            (k + 1 + ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
            (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)
            (toff + sch.N * (Bc + 1) +
              ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s.val).sum)
            (upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
            [upClimb k sch.m sch.ℓ (schemeNmax sch) s]).length
          = 2 + upRest Bc (child s) := by
        intro s
        rw [List.length_cons, ih s]
        rw [upHead_of_ne _ _ (by omega)]
        simp only [List.length_nil, List.length_singleton]
        omega
      simp only [upSched, upRest, Node.N, List.length_append, List.length_map,
        List.length_range, length_flatten_ofFn]
      rw [Finset.sum_congr rfl (fun x _ => hstep x)]
      omega
theorem upCnt_le (Bc Bℓ : ℕ) (hB : 1 ≤ Bℓ) :
    ∀ (T : Node), UpEllOK Bℓ T → ∀ (p D : ℕ), p + T.depth ≤ D →
      upCnt Bc T p ≤ T.nodeCount * (D + 2 * Bℓ + Bc) := by
  intro T
  induction T with
  | store N =>
      intro _ p D h
      have h1 : (Node.store N).depth = 1 := rfl
      simp only [upCnt, Node.nodeCount, Node.depth] at h ⊢
      omega
  | cr N t =>
      intro _ p D h
      have h1 : (Node.cr N t).depth = 1 := rfl
      simp only [upCnt, Node.nodeCount, Node.depth] at h ⊢
      omega
  | direct sch t =>
      intro hE p D h
      have h1 : (Node.direct sch t).depth = 1 := rfl
      have hℓ : sch.ℓ ≤ Bℓ := hE
      simp only [upCnt, Node.nodeCount, Node.depth] at h ⊢
      omega
  | recursive sch t Xs Ys child ih =>
      intro hE p D h
      have hEll : sch.ℓ ≤ Bℓ := hE.1
      have hchild : ∀ s : Fin sch.ℓ, upCnt Bc (child s) (p + 1)
          ≤ (child s).nodeCount * (D + 2 * Bℓ + Bc) := by
        intro s
        have hsup : (child s).depth ≤ (Node.recursive sch t Xs Ys child).depth - 1 := by
          have h2 : (Node.recursive sch t Xs Ys child).depth
              = 1 + (Finset.univ.sup fun s => (child s).depth) := rfl
          have h3 : (child s).depth ≤ Finset.univ.sup (fun s => (child s).depth) :=
            Finset.le_sup (f := fun s => (child s).depth) (Finset.mem_univ s)
          omega
        have hd1 : 1 ≤ (Node.recursive sch t Xs Ys child).depth := one_le_depth _
        refine ih s (hE.2 s) (p + 1) D ?_
        omega
      simp only [upCnt, Node.nodeCount, Node.depth] at h ⊢
      have hsum : (∑ s : Fin sch.ℓ, upCnt Bc (child s) (p + 1))
          ≤ (∑ s : Fin sch.ℓ, (child s).nodeCount) * (D + 2 * Bℓ + Bc) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun s _ => hchild s
      set S : ℕ := ∑ s : Fin sch.ℓ, (child s).nodeCount with hSdef
      have hp : 1 + p + Bc + sch.ℓ ≤ D + 2 * Bℓ + Bc := by omega
      have hexp : (1 + S) * (D + 2 * Bℓ + Bc) = (D + 2 * Bℓ + Bc) + S * (D + 2 * Bℓ + Bc) := by ring
      rw [hexp]
      linarith only [hsum, hp]
theorem one_add_upRest_le_upCnt (Bc : ℕ) (T : Node) :
    ∀ p : ℕ, 1 + upRest Bc T ≤ upCnt Bc T p := by
  induction T with
  | store N =>
      intro p
      simp only [upRest, upCnt]
      omega
  | cr N t =>
      intro p
      simp only [upRest, upCnt]
      omega
  | direct sch t =>
      intro p
      simp only [upRest, upCnt]
      omega
  | recursive sch t Xs Ys child ih =>
      intro p
      simp only [upRest, upCnt]
      have hsum : (∑ s : Fin sch.ℓ, (1 + upRest Bc (child s)))
          ≤ ∑ s : Fin sch.ℓ, upCnt Bc (child s) (p + 1) :=
        Finset.sum_le_sum fun s _ => ih s (p + 1)
      have hexp : (∑ s : Fin sch.ℓ, (2 + upRest Bc (child s))) =
          sch.ℓ + ∑ s : Fin sch.ℓ, (1 + upRest Bc (child s)) := by
        simp only [show ∀ a : ℕ, 2 + a = 1 + (1 + a) from by omega,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, Nat.mul_one]
      rw [hexp]
      omega
theorem upSched_count_le (CR : CRFamily) (Bc Bℓ colBase : ℕ) (hB : 1 ≤ Bℓ) (T : Node)
    (hE : UpEllOK Bℓ T) (k base toff sav : ℕ) :
    (upSched CR Bc colBase T k base toff sav []).length ≤ T.nodeCount * (T.depth + 2 * Bℓ + Bc) := by
  rw [upSched_length]
  have hh : (upHead (Node.N T) k).length ≤ 1 := upHead_length_le _ _
  have h1 : 1 + upRest Bc T ≤ upCnt Bc T 0 := one_add_upRest_le_upCnt Bc T 0
  have h2 : upCnt Bc T 0 ≤ T.nodeCount * (T.depth + 2 * Bℓ + Bc) :=
    upCnt_le Bc Bℓ hB T hE 0 T.depth (by omega)
  simp only [List.length_nil, Nat.add_zero]
  omega
def upTabSlot (CR : CRFamily) (Bc : ℕ) (N t c d : ℕ) : ℕ :=
  if d = 0 then (CR.col N t c).card
  else ((CR.col N t c).sort (· ≤ ·)).getD (d - 1) 0
def upTabAt (CR : CRFamily) (Bc : ℕ) (N t toff a : ℕ) : ℕ :=
  upTabSlot CR Bc N t ((a - toff) / (Bc + 1)) ((a - toff) % (Bc + 1))
def upTabFun (CR : CRFamily) (Bc : ℕ) : (T : Node) → ℕ → ℕ → ℕ
  | .store _, _, _ => 0
  | .cr N t, toff, a =>
      if toff ≤ a ∧ a < toff + N * (Bc + 1) then upTabAt CR Bc N t toff a else 0
  | .direct sch t, toff, a =>
      if toff ≤ a ∧ a < toff + sch.N * (Bc + 1) then upTabAt CR Bc sch.N t toff a else 0
  | .recursive sch t _ _ child, toff, a =>
      if toff ≤ a ∧ a < toff + sch.N * (Bc + 1) then upTabAt CR Bc sch.N t toff a
      else if a < toff + (sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s)) then
        ∑ s : Fin sch.ℓ, upTabFun CR Bc (child s) (upKidOff Bc sch child toff s.val) a
      else 0
theorem blockOf_self (R : Node) : BlockOf R 0 (schemeNodes R) := by
  intro j _
  rw [Nat.zero_add]
theorem up_words_cover_budget (W M : ℕ) (hW : 0 < W) : M ≤ wordsOf W M * W := by
  have hd := Nat.mod_add_div (M + W - 1) W
  have hm := Nat.mod_lt (M + W - 1) hW
  rw [Nat.mul_comm W _] at hd
  unfold wordsOf
  omega
theorem fits_mono_word (spec : TableSpec) {W V : ℕ} (hWV : W ≤ V) (h : spec.Fits W) : spec.Fits V := by
  have hp : 2 ^ W ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) hWV
  exact ⟨h.1.trans hp, h.2.1.trans hp, fun a ha => (h.2.2.1 a ha).trans hp,
    fun p hp' => ⟨(h.2.2.2 p hp').1.trans hp, (h.2.2.2 p hp').2.trans hp⟩⟩
theorem wordsOf_antitone_word {W V M : ℕ} (hW : 0 < W) (hWV : W ≤ V) : wordsOf V M ≤ wordsOf W M := by
  let Q := wordsOf W M
  have hV : 0 < V := lt_of_lt_of_le hW hWV
  have hM : M ≤ Q * V := (up_words_cover_budget W M hW).trans (Nat.mul_le_mul_left Q hWV)
  change (M + V - 1) / V ≤ Q
  have hh : (M + V - 1) / V < Q + 1 := by
    rw [Nat.div_lt_iff_lt_mul hV]
    have he : (Q + 1) * V = Q * V + V := by ring
    rw [he]
    omega
  exact Nat.le_of_lt_succ hh
theorem bits_le_wordSquare (W M : ℕ) (hW : 0 < W) (hWords : wordsOf W M ≤ 2 ^ W) :
    M ≤ (2 ^ W) ^ 2 := by
  calc
    M ≤ wordsOf W M * W := up_words_cover_budget W M hW
    _ ≤ 2 ^ W * 2 ^ W := Nat.mul_le_mul hWords (Nat.le_of_lt (Nat.lt_two_pow_self (n := W)))
    _ = (2 ^ W) ^ 2 := by ring
def upWideWord (W : ℕ) : ℕ := 8 * W
theorem upWideWord_pow (W : ℕ) : 2 ^ upWideWord W = (2 ^ W) ^ 8 := by
  unfold upWideWord
  rw [← pow_mul]
  congr 1
  omega
theorem upWideWord_ge (W : ℕ) : W ≤ upWideWord W := by unfold upWideWord; omega
end LinearSetReconciliation327.Main
end
namespace LinearSetReconciliation327.Main
theorem upCoarse_sizes (R nc d B S U Bc L tab M C : ℕ) (hR : 1 ≤ R)
    (hB : B ≤ R) (hS : S ≤ R) (hU : U ≤ R) (hBc : Bc ≤ 4 * R ^ 3)
    (hNc : nc ≤ 1 + B * S) (hD : d ≤ S + 1)
    (hL : L ≤ nc * (d + 2 * B + Bc))
    (hTab : tab ≤ nc * U * (Bc + 1)) (hM : M ≤ R ^ 2) (hC : C ≤ M + nc) :
    nc ≤ 2 * R ^ 2 ∧ d ≤ 2 * R ∧ L ≤ 16 * R ^ 5 ∧
      tab ≤ 10 * R ^ 6 ∧ C ≤ 3 * R ^ 2 := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR13 : R ≤ R ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hR (by norm_num : 1 ≤ (3 : ℕ))
  have hBS : B * S ≤ R ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hB hS
  have hNc2 : nc ≤ 2 * R ^ 2 := by omega
  have hD2 : d ≤ 2 * R := by omega
  have hBlock : d + 2 * B + Bc ≤ 8 * R ^ 3 := by omega
  have hL5 : L ≤ 16 * R ^ 5 := by
    calc
      L ≤ nc * (d + 2 * B + Bc) := hL
      _ ≤ (2 * R ^ 2) * (8 * R ^ 3) := Nat.mul_le_mul hNc2 hBlock
      _ = 16 * R ^ 5 := by ring
  have hBcs : Bc + 1 ≤ 5 * R ^ 3 := by omega
  have hTab6 : tab ≤ 10 * R ^ 6 := by
    calc
      tab ≤ nc * U * (Bc + 1) := hTab
      _ ≤ (2 * R ^ 2) * R * (5 * R ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul hNc2 hU) hBcs
      _ = 10 * R ^ 6 := by ring
  exact ⟨hNc2, hD2, hL5, hTab6, by omega⟩
end LinearSetReconciliation327.Main
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem UpDimsBound.mono {Q F : ℕ} (hQF : Q ≤ F) : ∀ T,
    UpDimsBound Q T → UpDimsBound F T := by
  intro T
  induction T with
  | store N => intro h; exact h.trans hQF
  | cr N t => intro h; exact h.trans hQF
  | direct sch t => intro h; exact ⟨h.1.trans hQF, h.2.1.trans hQF, h.2.2.1.trans hQF, h.2.2.2.trans hQF⟩
  | recursive sch t Xs Ys child ih =>
      intro h
      exact ⟨h.1.trans hQF, h.2.1.trans hQF, h.2.2.1.trans hQF,
        h.2.2.2.1.trans hQF, fun s => ih s (h.2.2.2.2 s)⟩
theorem UpDimsBound.to_ell {Q : ℕ} : ∀ T, UpDimsBound Q T → UpEllOK Q T := by
  intro T
  induction T with
  | store N => intro h; exact trivial
  | cr N t => intro h; exact trivial
  | direct sch t => intro h; exact h.2.2.1
  | recursive sch t Xs Ys child ih => intro h; exact ⟨h.2.2.1, fun s => ih s (h.2.2.2.2 s)⟩
theorem upCoarse_safety (R : ℕ) (hR : 256 ≤ R) : 512 * R ^ 6 < R ^ 8 := by
  have h0 : 0 < R := by omega
  have hSquare : 512 < R ^ 2 := by nlinarith
  calc
    512 * R ^ 6 < R ^ 2 * R ^ 6 := Nat.mul_lt_mul_of_pos_right hSquare (pow_pos h0 _)
    _ = R ^ 8 := by ring
def upRootCount (Bc : ℕ) (T : Node) : ℕ := 1 + upRest Bc T
def upRootBase (Bc : ℕ) (T : Node) : ℕ := 8 + 16 * upRootCount Bc T
def upRootSlot (CR : CRFamily) (W : ℕ) (T : Node) : ℕ :=
  wordsOf (upWideWord W) (synLen CR T) + 2 * (schemeNodes T).length
def upRootItems (CR : CRFamily) (W Bc : ℕ) (T : Node) : List UpIt :=
  upSched CR Bc (upRootBase Bc T) T 0 0 0 (upRootSlot CR W T) []
def upRootDet (CR : CRFamily) (W Bc : ℕ) (T : Node) : ℕ → ℕ :=
  upDet (upRootCount Bc T) (upWideWord W) (upRootBase Bc T) (upRootItems CR W Bc T)
    (upTabFun CR Bc T 0)
structure UpRootLayoutFits (CR : CRFamily) (W Bc : ℕ) (T : Node) : Prop where
  word : 1 < 2 ^ upWideWord W
  length_eq : (upRootItems CR W Bc T).length = upRootCount Bc T
  count : (upRootItems CR W Bc T).length < 2 ^ upWideWord W
  address : 8 + 16 * (upRootItems CR W Bc T).length < 2 ^ upWideWord W
  colBase : 4 < upRootBase Bc T
  table_end : upRootBase Bc T + upTabLen Bc T < 2 ^ upWideWord W
  bits : synLen CR T < 2 ^ upWideWord W
  universe_fits : T.N ≤ 2 ^ upWideWord W
  room : UpSaveRoom (wordsOf (upWideWord W) (synLen CR T)) (upRootSlot CR W T) T
  fields : ∀ j (hj : j < (upRootItems CR W Bc T).length), ∀ t, t < 16 →
    upRootDet CR W Bc T (8 + 16 * j + t) % 2 ^ upWideWord W = ((upRootItems CR W Bc T)[j]).fld t
  saves : ∀ it ∈ upRootItems CR W Bc T, it.sav + 1 < 2 ^ upWideWord W
  count_read : upRootDet CR W Bc T 0 % 2 ^ upWideWord W = (upRootItems CR W Bc T).length
theorem upRoot_layout_fits (CR : CRFamily) (P : HintParams) (W Bc U : ℕ)
    (T : Node) (hT : IsSchemeTree P T) (hW : 8 ≤ W)
    (hFits : (hintSpec T).Fits W) (hWords : wordsOf W (synLen CR T) ≤ 2 ^ W)
    (hStatic : UpTreeStatic CR Bc U T) (hU : U ≤ 2 ^ W) (hN : 0 < T.N)
    (hBc : Bc ≤ 4 * (2 ^ W) ^ 3) : UpRootLayoutFits CR W Bc T := by
  let R := 2 ^ W
  let F := 512 * R ^ 6
  let V := upWideWord W
  let items := upRootItems CR W Bc T
  let colBase := upRootBase Bc T
  let slot := upRootSlot CR W T
  let M := synLen CR T
  let S := (schemeNodes T).length
  have hWpos : 0 < W := by omega
  have hBcR : Bc ≤ 4 * R ^ 3 := hBc
  have hRlarge : 256 ≤ R := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hW
    norm_num at h
    exact h
  have hR1 : 1 ≤ R := by omega
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR1
  have h16 : R ≤ R ^ 6 := by simpa only [pow_one] using Nat.pow_le_pow_right hR1 (by norm_num : 1 ≤ (6 : ℕ))
  have h26 : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right hR1 (by norm_num)
  have h36 : R ^ 3 ≤ R ^ 6 := Nat.pow_le_pow_right hR1 (by norm_num)
  have h56 : R ^ 5 ≤ R ^ 6 := Nat.pow_le_pow_right hR1 (by norm_num)
  have hRF : R ≤ F := by dsimp only [F]; omega
  have hF3 : 3 ≤ F := by dsimp only [F]; omega
  have hFword : F < 2 ^ V := by
    change 512 * R ^ 6 < 2 ^ upWideWord W
    rw [upWideWord_pow]
    exact upCoarse_safety R hRlarge
  have hS : S ≤ R := by
    simpa only [hintSpec, permSizesOf, List.length_map] using hFits.1
  have hDims : UpDimsBound R T := upDims_of_tables CR P T W Bc U hFits hU T hT 0 (blockOf_self T) hStatic hN
  have hEll : UpEllOK R T := UpDimsBound.to_ell T hDims
  have hNc : T.nodeCount ≤ 1 + R * S := up_nodeCount_le_schemeNodes R T hEll
  have hD : T.depth ≤ S + 1 := up_depth_le_schemeNodes T
  have hL : items.length ≤ T.nodeCount * (T.depth + 2 * R + Bc) :=
    upSched_count_le CR Bc R colBase hR1 T hEll 0 0 0 slot
  have hTab : upTabLen Bc T ≤ T.nodeCount * U * (Bc + 1) := upTabLen_le_static CR Bc U T hStatic
  have hM : M ≤ R ^ 2 := bits_le_wordSquare W M hWpos hWords
  obtain ⟨hNc2, hD2, hL5, hTab6, hZero⟩ := upCoarse_sizes R T.nodeCount T.depth R S U Bc
    items.length (upTabLen Bc T) M 0 hR1 le_rfl hS hU hBcR hNc hD hL hTab hM (by omega)
  have hCount : items.length = upRootCount Bc T := by
    change (upSched CR Bc colBase T 0 0 0 slot []).length = 1 + upRest Bc T
    rw [upSched_length, upHead_zero]
    simp only [List.length_singleton, List.length_nil, Nat.add_zero]
  have hCol : colBase = 8 + 16 * items.length := by
    change 8 + 16 * upRootCount Bc T = 8 + 16 * items.length
    rw [hCount]
  have hUp : 16 * items.length ≤ 256 * R ^ 6 := by
    calc
      16 * items.length ≤ 16 * (16 * R ^ 5) := Nat.mul_le_mul_left 16 hL5
      _ = 256 * R ^ 5 := by ring
      _ ≤ 256 * R ^ 6 := Nat.mul_le_mul_left 256 h56
  have hTabF : colBase + upTabLen Bc T ≤ F := by dsimp only [F]; omega
  have hBcF : Bc + 1 ≤ F := by
    have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
    dsimp only [F]
    omega
  have hPayload : wordsOf V M ≤ R :=
    (wordsOf_antitone_word hWpos (upWideWord_ge W)).trans hWords
  have hSlot : slot + 1 ≤ F := by
    change wordsOf V M + 2 * S + 1 ≤ F
    dsimp only [F]
    omega
  have hMF : M ≤ F := by dsimp only [F]; omega
  have hFld : ∀ it ∈ items, UpFldBound F it := by
    apply upSched_fields_le CR Bc colBase F hF3 hBcF T 0 0 0 slot []
      (UpDimsBound.mono hRF T hDims)
    · simpa only [Nat.zero_add] using hS.trans hRF
    · simpa only [Nat.zero_add] using hMF
    · simpa only [Nat.add_zero] using hTabF
    · omega
    · simp
  have hSave : ∀ it ∈ items, it.sav + 1 < 2 ^ V :=
    upSched_sav_word CR Bc colBase T 0 0 0 slot V (hSlot.trans_lt hFword) (hBcF.trans_lt hFword)
  have hAddr : 8 + 16 * items.length < 2 ^ V := by omega
  have hLen : items.length < 2 ^ V := by omega
  have hFields := upDet_fields_from_le (upRootCount Bc T) V colBase F items
    (upTabFun CR Bc T 0) hFword (by omega) hFld
  have hWord : 1 < 2 ^ V := (by omega : 1 ≤ F).trans_lt hFword
  have hCol4 : 4 < colBase := by omega
  refine ⟨hWord, hCount, hLen, hAddr, hCol4, hTabF.trans_lt hFword,
    hMF.trans_lt hFword, hStatic.universe.trans (hU.trans (hRF.trans hFword.le)), ?_, hFields, hSave, ?_⟩
  · exact le_rfl
  · change upDet (upRootCount Bc T) V colBase items (upTabFun CR Bc T 0) 0 % 2 ^ V = items.length
    rw [upDet_zero, ← hCount, Nat.mod_eq_of_lt hLen]
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
theorem upTabSlot_zero (CR : CRFamily) (Bc N t c : ℕ) :
    upTabSlot CR Bc N t c 0 = (CR.col N t c).card := by
  unfold upTabSlot
  simp
theorem upTabSlot_succ (CR : CRFamily) (Bc N t c q : ℕ) :
    upTabSlot CR Bc N t c (1 + q) = ((CR.col N t c).sort (· ≤ ·)).getD q 0 := by
  unfold upTabSlot
  rw [if_neg (by omega : ¬ (1 + q = 0))]
  rw [show 1 + q - 1 = q from by omega]
theorem upTab_div (Bc c d : ℕ) (hd : d < Bc + 1) : ((Bc + 1) * c + d) / (Bc + 1) = c := by
  rw [Nat.mul_add_div (show 0 < Bc + 1 by omega), Nat.div_eq_of_lt hd, Nat.add_zero]
theorem upTab_mod (Bc c d : ℕ) (hd : d < Bc + 1) : ((Bc + 1) * c + d) % (Bc + 1) = d := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
theorem upTab_div_zero (Bc c : ℕ) : ((Bc + 1) * c) / (Bc + 1) = c := by
  have h := upTab_div Bc c 0 (by omega)
  simpa using h
theorem upTab_mod_zero (Bc c : ℕ) : ((Bc + 1) * c) % (Bc + 1) = 0 := by
  have h := upTab_mod Bc c 0 (by omega)
  simpa using h
theorem mul_succ_le (Bc N c : ℕ) (h : c < N) : (Bc + 1) * c + (Bc + 1) ≤ N * (Bc + 1) := by
  rw [← Nat.mul_succ, Nat.mul_comm N (Bc + 1)]
  exact Nat.mul_le_mul_left (Bc + 1) (by omega)
theorem addr_lt (Bc N c : ℕ) (h : c < N) : (Bc + 1) * c < N * (Bc + 1) := by
  have h1 := mul_succ_le Bc N c h
  have h2 : (0 : ℕ) < Bc + 1 := by omega
  omega
theorem slot_lt (Bc N c q : ℕ) (hc : c < N) (hq : q < Bc) : (Bc + 1) * c + 1 + q < N * (Bc + 1) := by
  have h1 := mul_succ_le Bc N c hc
  have h2 : 1 + q < Bc + 1 := by omega
  omega
theorem addr_lt_toff (Bc N c toff : ℕ) (h : c < N) : toff + (Bc + 1) * c < toff + N * (Bc + 1) := by
  have h1 := addr_lt Bc N c h
  omega
theorem slot_lt_toff (Bc N c q toff : ℕ) (hc : c < N) (hq : q < Bc) :
    toff + (Bc + 1) * c + 1 + q < toff + N * (Bc + 1) := by
  have h1 := slot_lt Bc N c q hc hq
  omega
theorem upKidOff_ge (Bc : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node) (toff s : ℕ) :
    toff + sch.N * (Bc + 1) ≤ upKidOff Bc sch child toff s := by
  unfold upKidOff
  omega
def upTabVal (CR : CRFamily) (Bc : ℕ) : Node → ℕ → ℕ
  | .store _, _ => 0
  | .cr N t, i => upTabSlot CR Bc N t (i / (Bc + 1)) (i % (Bc + 1))
  | .direct sch t, i => upTabSlot CR Bc sch.N t (i / (Bc + 1)) (i % (Bc + 1))
  | .recursive sch t _ _ _, i => upTabSlot CR Bc sch.N t (i / (Bc + 1)) (i % (Bc + 1))
theorem upTabFun_store (CR : CRFamily) (Bc N toff a : ℕ) :
    upTabFun CR Bc (.store N) toff a = 0 := rfl
theorem upTabFun_cr (CR : CRFamily) (Bc N t toff a : ℕ) :
    upTabFun CR Bc (.cr N t) toff a
      = if toff ≤ a ∧ a < toff + N * (Bc + 1) then upTabAt CR Bc N t toff a else 0 := rfl
theorem upTabFun_direct (CR : CRFamily) (Bc : ℕ) (sch : RowScheme) (t toff a : ℕ) :
    upTabFun CR Bc (.direct sch t) toff a
      = if toff ≤ a ∧ a < toff + sch.N * (Bc + 1) then upTabAt CR Bc sch.N t toff a else 0 := rfl
theorem upTabFun_rec (CR : CRFamily) (Bc : ℕ) (sch : RowScheme) (t : ℕ) (X Y : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) (toff a : ℕ) :
    upTabFun CR Bc (.recursive sch t X Y child) toff a
      = if toff ≤ a ∧ a < toff + sch.N * (Bc + 1) then upTabAt CR Bc sch.N t toff a
        else if a < toff + (sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s)) then
          ∑ s : Fin sch.ℓ, upTabFun CR Bc (child s) (upKidOff Bc sch child toff s.val) a
        else 0 := rfl
theorem upTabVal_store (CR : CRFamily) (Bc N i : ℕ) : upTabVal CR Bc (.store N) i = 0 := rfl
theorem upTabVal_cr (CR : CRFamily) (Bc N t i : ℕ) :
    upTabVal CR Bc (.cr N t) i = upTabSlot CR Bc N t (i / (Bc + 1)) (i % (Bc + 1)) := rfl
theorem upTabVal_direct (CR : CRFamily) (Bc : ℕ) (sch : RowScheme) (t i : ℕ) :
    upTabVal CR Bc (.direct sch t) i = upTabSlot CR Bc sch.N t (i / (Bc + 1)) (i % (Bc + 1)) :=
  rfl
theorem upTabVal_rec (CR : CRFamily) (Bc : ℕ) (sch : RowScheme) (t : ℕ) (X Y : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) (i : ℕ) :
    upTabVal CR Bc (.recursive sch t X Y child) i
      = upTabSlot CR Bc sch.N t (i / (Bc + 1)) (i % (Bc + 1)) := rfl
theorem upTabFun_supp (CR : CRFamily) (Bc : ℕ) :
    ∀ (T : Node) (toff a : ℕ),
      upTabFun CR Bc T toff a ≠ 0 → toff ≤ a ∧ a < toff + upTabLen Bc T := by
  intro T
  induction T with
  | store N =>
      intro toff a h
      rw [upTabFun_store] at h
      exact absurd rfl h
  | cr N t =>
      intro toff a h
      rw [upTabFun_cr] at h
      by_cases hc : toff ≤ a ∧ a < toff + N * (Bc + 1)
      · rw [if_pos hc] at h
        exact ⟨hc.1, hc.2⟩
      · rw [if_neg hc] at h
        exact absurd rfl h
  | direct sch t =>
      intro toff a h
      rw [upTabFun_direct] at h
      by_cases hc : toff ≤ a ∧ a < toff + sch.N * (Bc + 1)
      · rw [if_pos hc] at h
        exact ⟨hc.1, hc.2⟩
      · rw [if_neg hc] at h
        exact absurd rfl h
  | recursive sch t X Y child ih =>
      have hU : upTabLen Bc (.recursive sch t X Y child)
          = sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s) := rfl
      intro toff a h
      rw [upTabFun_rec] at h
      by_cases hc : toff ≤ a ∧ a < toff + sch.N * (Bc + 1)
      · rw [if_pos hc] at h
        refine ⟨hc.1, ?_⟩
        have h0 : (0 : ℕ) ≤ ∑ s : Fin sch.ℓ, upTabLen Bc (child s) := Nat.zero_le _
        rw [hU]
        omega
      · rw [if_neg hc] at h
        by_cases hc2 : a < toff + (sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s))
        · rw [if_pos hc2] at h
          have hex : ∃ s : Fin sch.ℓ,
              upTabFun CR Bc (child s) (upKidOff Bc sch child toff s.val) a ≠ 0 := by
            by_contra hcon
            push_neg at hcon
            exact h (Finset.sum_eq_zero (fun s _ => hcon s))
          obtain ⟨s, hs⟩ := hex
          obtain ⟨hs1, hs2⟩ := ih s (upKidOff Bc sch child toff s.val) a hs
          refine ⟨?_, ?_⟩
          · have h1 := upKidOff_ge Bc sch child toff s.val
            omega
          · have h1 : upKidOff Bc sch child toff s.val + upTabLen Bc (child s)
                ≤ toff + (sch.N * (Bc + 1) + ∑ i : Fin sch.ℓ, upTabLen Bc (child i)) :=
              upKidOff_le_top Bc sch child toff s.val s.isLt
            rw [hU]
            omega
        · rw [if_neg hc2] at h
          exact absurd rfl h
theorem upTabFun_val (CR : CRFamily) (Bc : ℕ) :
    ∀ (T : Node) (toff a : ℕ), toff ≤ a → a < toff + upOwn Bc T →
      upTabFun CR Bc T toff a = upTabVal CR Bc T (a - toff) := by
  intro T
  induction T with
  | store N =>
      intro toff a h1 h2
      rw [upTabFun_store, upTabVal_store]
  | cr N t =>
      intro toff a h1 h2
      rw [upTabFun_cr]
      rw [if_pos ⟨h1, by simpa [upOwn] using h2⟩]
      rfl
  | direct sch t =>
      intro toff a h1 h2
      rw [upTabFun_direct]
      rw [if_pos ⟨h1, by simpa [upOwn] using h2⟩]
      rfl
  | recursive sch t X Y child ih =>
      intro toff a h1 h2
      rw [upTabFun_rec]
      rw [if_pos ⟨h1, by simpa [upOwn] using h2⟩]
      rfl
theorem upTabFun_child (CR : CRFamily) (Bc : ℕ) (sch : RowScheme) (t : ℕ)
    (X Y : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node) (toff s a : ℕ) (hs : s < sch.ℓ)
    (hlo : upKidOff Bc sch child toff s ≤ a)
    (hhi : a < upKidOff Bc sch child toff s + upTabLen Bc (child ⟨s, hs⟩)) :
    upTabFun CR Bc (.recursive sch t X Y child) toff a
      = upTabFun CR Bc (child ⟨s, hs⟩) (upKidOff Bc sch child toff s) a := by
  have hge := upKidOff_ge Bc sch child toff s
  have htop := upKidOff_le_top Bc sch child toff s hs
  have hlt : a < toff + (sch.N * (Bc + 1) + ∑ i : Fin sch.ℓ, upTabLen Bc (child i)) := by omega
  rw [upTabFun_rec, if_neg (by omega : ¬ (toff ≤ a ∧ a < toff + sch.N * (Bc + 1))), if_pos hlt]
  have hsum : (∑ b : Fin sch.ℓ, upTabFun CR Bc (child b) (upKidOff Bc sch child toff b.val) a)
      = upTabFun CR Bc (child ⟨s, hs⟩) (upKidOff Bc sch child toff s) a := by
    refine Finset.sum_eq_single (⟨s, hs⟩ : Fin sch.ℓ) ?_ ?_
    · intro b _ hb
      by_contra hne
      obtain ⟨hb1, hb2⟩ := upTabFun_supp CR Bc (child b) (upKidOff Bc sch child toff b.val) a hne
      have hbval : b.val ≠ s := fun h => hb (Fin.ext h)
      rcases lt_or_gt_of_ne hbval with hlt' | hgt'
      · have hle : upKidOff Bc sch child toff b.val + upTabLen Bc (child b)
            ≤ upKidOff Bc sch child toff s := by
          rw [← upKidOff_succ Bc sch child toff b.val b.isLt]
          exact upKidOff_mono Bc sch child toff (b.val + 1) s (by omega)
        omega
      · have hle : upKidOff Bc sch child toff s + upTabLen Bc (child ⟨s, hs⟩)
            ≤ upKidOff Bc sch child toff b.val := by
          rw [← upKidOff_succ Bc sch child toff s hs]
          exact upKidOff_mono Bc sch child toff (s + 1) b.val (by omega)
        omega
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hsum]
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upTabFullTree_congr (CR : CRFamily) (Bc : ℕ) :
    ∀ (T : Node) (toff : ℕ) (tab tab' : ℕ → ℕ),
      (∀ a : ℕ, toff ≤ a → a < toff + upTabLen Bc T → tab a = tab' a) →
      UpTabFullTree CR Bc tab T toff → UpTabFullTree CR Bc tab' T toff := by
  intro T
  induction T with
  | store N =>
      intro toff tab tab' hag hOK
      exact hOK
  | cr N t =>
      intro toff tab tab' hag hOK
      have hOK' : UpTabFullAt CR Bc tab N t toff := hOK
      intro c hcc
      have hb1 : toff + (Bc + 1) * c < toff + upTabLen Bc (.cr N t) := by
        have h := addr_lt_toff Bc N c toff hcc
        simpa [upTabLen] using h
      constructor
      · rw [← hag _ (by omega) hb1]
        exact (hOK' c hcc).1
      · intro q hq
        have hqB : q < Bc := hq
        have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upTabLen Bc (.cr N t) := by
          have h := slot_lt_toff Bc N c q toff hcc hqB
          simpa [upTabLen] using h
        rw [← hag _ (by omega) hb2]
        exact (hOK' c hcc).2 q hq
  | direct sch t =>
      intro toff tab tab' hag hOK
      have hOK' : UpTabFullAt CR Bc tab sch.N t toff := hOK
      intro c hcc
      have hb1 : toff + (Bc + 1) * c < toff + upTabLen Bc (.direct sch t) := by
        have h := addr_lt_toff Bc sch.N c toff hcc
        simpa [upTabLen] using h
      constructor
      · rw [← hag _ (by omega) hb1]
        exact (hOK' c hcc).1
      · intro q hq
        have hqB : q < Bc := hq
        have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upTabLen Bc (.direct sch t) := by
          have h := slot_lt_toff Bc sch.N c q toff hcc hqB
          simpa [upTabLen] using h
        rw [← hag _ (by omega) hb2]
        exact (hOK' c hcc).2 q hq
  | recursive sch t X Y child ih =>
      intro toff tab tab' hag hOK
      obtain ⟨hown, hkids⟩ := hOK
      refine ⟨?_, ?_⟩
      · intro c hcc
        have hb1 : toff + (Bc + 1) * c < toff + upTabLen Bc (.recursive sch t X Y child) := by
          have h1 := addr_lt_toff Bc sch.N c toff hcc
          have h2 : upOwn Bc (.recursive sch t X Y child) ≤ upTabLen Bc (.recursive sch t X Y child) :=
            upOwn_le_tabLen Bc _
          have h3 : upOwn Bc (.recursive sch t X Y child) = sch.N * (Bc + 1) := rfl
          rw [h3] at h2
          omega
        constructor
        · rw [← hag _ (by omega) hb1]
          exact (hown c hcc).1
        · intro q hq
          have hqB : q < Bc := hq
          have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upTabLen Bc (.recursive sch t X Y child) := by
            have h1 := slot_lt_toff Bc sch.N c q toff hcc hqB
            have h2 : upOwn Bc (.recursive sch t X Y child) ≤ upTabLen Bc (.recursive sch t X Y child) :=
              upOwn_le_tabLen Bc _
            have h3 : upOwn Bc (.recursive sch t X Y child) = sch.N * (Bc + 1) := rfl
            rw [h3] at h2
            omega
          rw [← hag _ (by omega) hb2]
          exact (hown c hcc).2 q hq
      · intro s
        refine ih s (upKidOff Bc sch child toff s.val) tab tab' ?_ (hkids s)
        intro a ha1 ha2
        have ha2' : a < upKidOff Bc sch child toff s.val + upTabLen Bc (child ⟨s.val, s.isLt⟩) := ha2
        have hge := upKidOff_ge Bc sch child toff s.val
        refine hag a (by omega) ?_
        have htop := upKidOff_le_top Bc sch child toff s.val s.isLt
        have hU : upTabLen Bc (.recursive sch t X Y child)
            = sch.N * (Bc + 1) + ∑ i : Fin sch.ℓ, upTabLen Bc (child i) := rfl
        rw [hU]
        omega
theorem upTabFullTree_self (CR : CRFamily) (Bc : ℕ) :
    ∀ (T : Node), ∀ (toff : ℕ),
      UpTabFullTree CR Bc (upTabFun CR Bc T toff) T toff := by
  intro T
  induction T with
  | store N =>
      intro toff
      exact trivial
  | cr N t =>
      intro toff c hcc
      have hb1 : toff + (Bc + 1) * c < toff + upOwn Bc (.cr N t) := by
        have h := addr_lt_toff Bc N c toff hcc
        simpa [upOwn] using h
      constructor
      · rw [upTabFun_val CR Bc (.cr N t) toff (toff + (Bc + 1) * c) (by omega) hb1,
          Nat.add_sub_cancel_left, upTabVal_cr, upTab_div_zero, upTab_mod_zero]
        exact upTabSlot_zero CR Bc N t c
      · intro q hq
        have hqB : q < Bc := hq
        have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upOwn Bc (.cr N t) := by
          have h := slot_lt_toff Bc N c q toff hcc hqB
          simpa [upOwn] using h
        rw [upTabFun_val CR Bc (.cr N t) toff (toff + (Bc + 1) * c + 1 + q) (by omega) hb2,
          show toff + (Bc + 1) * c + 1 + q - toff = (Bc + 1) * c + 1 + q from by omega,
          upTabVal_cr, show (Bc + 1) * c + 1 + q = (Bc + 1) * c + (1 + q) from by omega,
          upTab_div Bc c (1 + q) (by omega), upTab_mod Bc c (1 + q) (by omega)]
        exact upTabSlot_succ CR Bc N t c q
  | direct sch t =>
      intro toff c hcc
      have hb1 : toff + (Bc + 1) * c < toff + upOwn Bc (.direct sch t) := by
        have h := addr_lt_toff Bc sch.N c toff hcc
        simpa [upOwn] using h
      constructor
      · rw [upTabFun_val CR Bc (.direct sch t) toff (toff + (Bc + 1) * c) (by omega) hb1,
          Nat.add_sub_cancel_left, upTabVal_direct, upTab_div_zero, upTab_mod_zero]
        exact upTabSlot_zero CR Bc sch.N t c
      · intro q hq
        have hqB : q < Bc := hq
        have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upOwn Bc (.direct sch t) := by
          have h := slot_lt_toff Bc sch.N c q toff hcc hqB
          simpa [upOwn] using h
        rw [upTabFun_val CR Bc (.direct sch t) toff (toff + (Bc + 1) * c + 1 + q) (by omega) hb2,
          show toff + (Bc + 1) * c + 1 + q - toff = (Bc + 1) * c + 1 + q from by omega,
          upTabVal_direct, show (Bc + 1) * c + 1 + q = (Bc + 1) * c + (1 + q) from by omega,
          upTab_div Bc c (1 + q) (by omega), upTab_mod Bc c (1 + q) (by omega)]
        exact upTabSlot_succ CR Bc sch.N t c q
  | recursive sch t X Y child ih =>
      intro toff
      refine ⟨?_, ?_⟩
      · intro c hcc
        have hb1 : toff + (Bc + 1) * c < toff + upOwn Bc (.recursive sch t X Y child) := by
          have h := addr_lt_toff Bc sch.N c toff hcc
          simpa [upOwn] using h
        constructor
        · rw [upTabFun_val CR Bc (.recursive sch t X Y child) toff (toff + (Bc + 1) * c)
            (by omega) hb1, Nat.add_sub_cancel_left, upTabVal_rec, upTab_div_zero,
            upTab_mod_zero]
          exact upTabSlot_zero CR Bc sch.N t c
        · intro q hq
          have hqB : q < Bc := hq
          have hb2 : toff + (Bc + 1) * c + 1 + q < toff + upOwn Bc (.recursive sch t X Y child) := by
            have h := slot_lt_toff Bc sch.N c q toff hcc hqB
            simpa [upOwn] using h
          rw [upTabFun_val CR Bc (.recursive sch t X Y child) toff (toff + (Bc + 1) * c + 1 + q)
            (by omega) hb2,
            show toff + (Bc + 1) * c + 1 + q - toff = (Bc + 1) * c + 1 + q from by omega,
            upTabVal_rec, show (Bc + 1) * c + 1 + q = (Bc + 1) * c + (1 + q) from by omega,
            upTab_div Bc c (1 + q) (by omega), upTab_mod Bc c (1 + q) (by omega)]
          exact upTabSlot_succ CR Bc sch.N t c q
      · intro s
        refine upTabFullTree_congr CR Bc (child s) (upKidOff Bc sch child toff s.val)
          (upTabFun CR Bc (child s) (upKidOff Bc sch child toff s.val))
          (upTabFun CR Bc (.recursive sch t X Y child) toff)
          ?_ (ih s (upKidOff Bc sch child toff s.val))
        intro a ha1 ha2
        exact (upTabFun_child CR Bc sch t X Y child toff s.val a s.isLt ha1 ha2).symm
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upRoot_localTree (CR : CRFamily) (P : HintParams) (W Bc U : ℕ)
    (T : Node) (hT : IsSchemeTree P T) (r : (hintSpec T).Seed) (i : ℕ)
    (hW : 8 ≤ W) (hFits : (hintSpec T).Fits W) (hU : U ≤ 2 ^ W)
    (hStatic : UpTreeStatic CR Bc U T) (hLayout : UpRootLayoutFits CR W Bc T) :
    UpLocalTree CR ((hintSpec T).env (upWideWord W) (upRootDet CR W Bc T) r)
      i Bc (upRootBase Bc T) T (hintKappa P T hT r) 0 0 0 := by
  have hVpos : 0 < upWideWord W := by unfold upWideWord; omega
  have hUV : U ≤ 2 ^ upWideWord W := hU.trans
    (Nat.pow_le_pow_right (by norm_num) (upWideWord_ge W))
  exact upLocalTree_of_tables CR P T (upWideWord W) (upRootCount Bc T) Bc (upRootBase Bc T) U
    (upRootItems CR W Bc T) (upTabFun CR Bc T 0) r i hLayout.word hVpos
    (fits_mono_word (hintSpec T) (upWideWord_ge W) hFits) hLayout.colBase hUV T hT 0 0 0
    (blockOf_self T) hStatic (upTabFullTree_self CR Bc T 0)
    (by simpa only [Nat.add_zero] using hLayout.table_end)
    (by simpa only [Nat.zero_add] using hLayout.bits)
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upApply_env_congr (E F : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff)
    (hWord : E.det (1 % 2 ^ E.W) = F.det (1 % 2 ^ E.W))
    (hCard : E.det (upvTb E i it a) = F.det (upvTb E i it a))
    (hElem : E.det (upvX5 E i it a) = F.det (upvX5 E i it a)) :
    upApply E i it a = upApply F i it a := by
  have eq0 : upvZ1 E it a = upvZ1 F it a := by
    simp only [upvZ1, hW, hPerm]
  have eq1 : upvZ2 E i it = upvZ2 F i it := by
    simp only [upvZ2, hW]
  have eq2 : upvZ3 E it = upvZ3 F it := by
    simp only [upvZ3, hW]
  have eq3 : upvZ4 E it a = upvZ4 F it a := by
    simp only [upvZ4, eq0, eq2, hW]
  have eq4 : upvZ5 E i it a = upvZ5 F i it a := by
    simp only [upvZ5, eq1, eq3, hW]
  have eq5 : upvZ6 E it a = upvZ6 F it a := by
    simp only [upvZ6, hW]
  have eq6 : upvZ7 E it = upvZ7 F it := by
    simp only [upvZ7, hW]
  have eq7 : upvZ8 E i it a = upvZ8 F i it a := by
    simp only [upvZ8, eq4, eq6, hW]
  have eq8 : upvImg E i it a = upvImg F i it a := by
    simp only [upvImg, eq5, eq7, hW]
  have eq9 : upvJ0 E i it a = upvJ0 F i it a := by
    simp only [upvJ0, eq8, hW]
  have eq10 : upvPos E i it a = upvPos F i it a := by
    simp only [upvPos, eq8, hW]
  have eq11 : upvY1 E i it a = upvY1 F i it a := by
    simp only [upvY1, eq9, hW]
  have eq12 : upvY2 E i it a = upvY2 F i it a := by
    simp only [upvY2, eq11, hW]
  have eq13 : upvCn E i it a = upvCn F i it a := by
    simp only [upvCn, eq12, hW]
  have eq14 : upvY3 E i it a = upvY3 F i it a := by
    simp only [upvY3, eq9, hW]
  have eq15 : upvQ E i it a = upvQ F i it a := by
    simp only [upvQ, eq14, hW]
  have eq16 : upvY4 E i it a = upvY4 F i it a := by
    simp only [upvY4, eq15, hW]
  have eq17 : upvY5 E i it a = upvY5 F i it a := by
    simp only [upvY5, eq10, eq16, hW]
  have eq18 : upvCoin E i it a = upvCoin F i it a := by
    simp only [upvCoin, eq17, hW, hCoef]
  have eq19 : upvY6 E i it a = upvY6 F i it a := by
    simp only [upvY6, eq18, hW]
  have eq20 : upvY7 E it = upvY7 F it := by
    simp only [upvY7, hW]
  have eq21 : upvY8 E i it a = upvY8 F i it a := by
    simp only [upvY8, eq19, eq20, hW]
  have eq22 : upvY9 E i it a = upvY9 F i it a := by
    simp only [upvY9, eq21, hW]
  have eq23 : upvY10 E i it a = upvY10 F i it a := by
    simp only [upvY10, eq22, hW]
  have eq24 : upvY11 E i it a = upvY11 F i it a := by
    simp only [upvY11, eq23, hW]
  have eq25 : upvFn E i it a = upvFn F i it a := by
    simp only [upvFn, eq24, hW]
  have eq26 : upvX1 E it = upvX1 F it := by
    simp only [upvX1, hW]
  have eq27 : upvX2 E i it a = upvX2 F i it a := by
    simp only [upvX2, eq18, hW]
  have eq28 : upvW0 E i it a = upvW0 F i it a := by
    simp only [upvW0, eq26, eq27, hW]
  have eq29 : upvX3 E i it a = upvX3 F i it a := by
    simp only [upvX3, eq13, hW]
  have eq30 : upvTb E i it a = upvTb F i it a := by
    simp only [upvTb, eq29, hW]
  have eq31 : upvCard E i it a = upvCard F i it a := by
    unfold upvCard
    rw [hCard, eq30, hW]
  have eq32 : upvValid E i it a = upvValid F i it a := by
    simp only [upvValid, eq31, hW]
  have eq33 : upvX4 E i it a = upvX4 F i it a := by
    simp only [upvX4, eq30, hW]
  have eq34 : upvX5 E i it a = upvX5 F i it a := by
    simp only [upvX5, eq33, hW]
  have eq35 : upvElem E i it a = upvElem F i it a := by
    unfold upvElem
    rw [hElem, eq34, hW]
  have eq36 : upvX6 E i it a = upvX6 F i it a := by
    simp only [upvX6, eq15, eq35, hW]
  have eq37 : upvX7 E i it a = upvX7 F i it a := by
    simp only [upvX7, eq36, hW]
  have eq38 : upvX8 E i it a = upvX8 F i it a := by
    simp only [upvX8, eq37, hW]
  have eq39 : upvBit E i it a = upvBit F i it a := by
    simp only [upvBit, eq15, eq38, hW]
  have eq40 : upvX9 E i it a = upvX9 F i it a := by
    simp only [upvX9, eq28, eq32, hW]
  have eq41 : upvX10 E i it a = upvX10 F i it a := by
    simp only [upvX10, eq40, hW]
  have eq42 : upvWt E i it a = upvWt F i it a := by
    simp only [upvWt, eq28, eq41, hW]
  have eq43 : upvX11 E i it a = upvX11 F i it a := by
    simp only [upvX11, eq25, eq42, hW]
  have eq44 : upvMask0 E i it a = upvMask0 F i it a := by
    simp only [upvMask0, eq43, hW]
  have eq45 : upvWw E = upvWw F := by
    unfold upvWw
    rw [hWord, hW]
  have eq46 : upvB1 E i it a = upvB1 F i it a := by
    simp only [upvB1, eq39, eq45, hW]
  have eq47 : upvSh E i it a = upvSh F i it a := by
    simp only [upvSh, eq46, hW]
  have eq48 : upvMask E i it a = upvMask F i it a := by
    simp only [upvMask, eq44, eq47, hW]
  have eq49 : upvWi E i it a = upvWi F i it a := by
    simp only [upvWi, eq39, eq45, hW]
  have eq50 : upvOld E i it a = upvOld F i it a := by
    simp only [upvOld, eq49, hW]
  have eq51 : upvNew E i it a = upvNew F i it a := by
    simp only [upvNew, eq48, eq50, hW]
  have eq52 : upApplyBody E i it a = upApplyBody F i it a := by
    simp only [upApplyBody, eq13, eq25, eq49, eq51]
  have eq53 : upvG2 E it = upvG2 F it := by
    simp only [upvG2, hW]
  have eq54 : upvG3 E it = upvG3 F it := by
    simp only [upvG3, hW]
  have eq55 : upvA2 E it = upvA2 F it := by
    simp only [upvA2, eq53, hW]
  have eq56 : upvA3 E it = upvA3 F it := by
    simp only [upvA3, eq54, hW]
  have eq57 : upvRt E it = upvRt F it := by
    simp only [upvRt, eq56, hW]
  have eq58 : upvSv E it = upvSv F it := by
    simp only [upvSv, eq55, eq57, hW]
  have eq59 : upvM0 E i it a = upvM0 F i it a := by
    simp only [upvM0, eq52, hW]
  have eq60 : upvM1 E i it a = upvM1 F i it a := by
    simp only [upvM1, eq52, hW]
  have eq61 : upvCnf E i it a = upvCnf F i it a := by
    simp only [upvCnf, eq13, eq57, eq59, hW]
  have eq62 : upvFnf E i it a = upvFnf F i it a := by
    simp only [upvFnf, eq25, eq57, eq60, hW]
  have eq63 : upvV0 E i it a = upvV0 F i it a := by
    simp only [upvV0, eq58, eq59, eq61, hW]
  have eq64 : upvV1 E i it a = upvV1 F i it a := by
    simp only [upvV1, eq58, eq60, eq62, hW]
  show upApply E i it a = upApply F i it a
  simp only [upApply, eq52, eq61, eq62, eq63, eq64]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def UpAbsBound (E : RAMEnv) (a : UpAbs) : Prop :=
  a.c < 2 ^ E.W ∧ a.f < 2 ^ E.W ∧ UpMemBound E a
theorem upApply_abs_bound (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) (ha : UpAbsBound E a) :
    UpAbsBound E (upApply E i it a) := by
  refine ⟨?_, ?_, upApply_mem_bound E i it a ha.2.2⟩
  · change upvCnf E i it a < 2 ^ E.W
    exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
  · change upvFnf E i it a < 2 ^ E.W
    exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
def UpDetReadEq (E F : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : Prop :=
  E.det (upvTb E i it a) = F.det (upvTb E i it a) ∧
    E.det (upvX5 E i it a) = F.det (upvX5 E i it a)
theorem upFold_env_congr (E F : RAMEnv) (i : ℕ)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff)
    (hWord : E.det (1 % 2 ^ E.W) = F.det (1 % 2 ^ E.W)) :
    ∀ L : List UpIt,
      (∀ it ∈ L, ∀ a : UpAbs, UpAbsBound E a → UpDetReadEq E F i it a) →
      ∀ a : UpAbs, UpAbsBound E a → upFold E i a L = upFold F i a L := by
  intro L
  induction L with
  | nil => intro hRead a ha; rfl
  | cons it L ih =>
      intro hRead a ha
      have hq := hRead it (by simp) a ha
      have happly := upApply_env_congr E F i it a hW hPerm hCoef hWord hq.1 hq.2
      change upFold E i (upApply E i it a) L = upFold F i (upApply F i it a) L
      rw [← happly]
      apply ih (fun it hi a ha => hRead it (List.mem_cons_of_mem _ hi) a ha)
      exact upApply_abs_bound E i it a ha
theorem UpLocalBitsCorrect.of_env (CR : CRFamily) (E F : RAMEnv) (i Bc colBase : ℕ)
    (T : Node) (r : T.Seed) (k base toff : ℕ)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff)
    (hWord : E.det (1 % 2 ^ E.W) = F.det (1 % 2 ^ E.W))
    (hRead : ∀ it ∈ upOwnItems CR Bc colBase T k base toff,
      ∀ a : UpAbs, UpAbsBound E a → UpDetReadEq E F i it a)
    (hOld : UpLocalBitsCorrect CR F i Bc colBase T r k base toff) :
    UpLocalBitsCorrect CR E i Bc colBase T r k base toff := by
  intro c f hcN hc hf hf01 mem hm addr
  have hrun := upFold_env_congr E F i hW hPerm hCoef hWord
    (upOwnItems CR Bc colBase T k base toff) hRead
    (⟨mem, c, f⟩ : UpAbs) ⟨hc, hf, hm⟩
  have hcF : c < 2 ^ F.W := by rw [← hW]; exact hc
  have hfF : f < 2 ^ F.W := by rw [← hW]; exact hf
  have hmF : ∀ a, mem a < 2 ^ F.W := by intro a; rw [← hW]; exact hm a
  calc
    (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff)).mem addr =
        (upFold F i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff)).mem addr :=
      congrArg (fun a : UpAbs => a.mem addr) hrun
    _ = mem addr ^^^ packSel F.W (if f = 1 then upNodeLocalBits CR T r base c else ∅) addr :=
      hOld c f hcN hcF hfF hf01 mem hmF addr
    _ = mem addr ^^^ packSel E.W (if f = 1 then upNodeLocalBits CR T r base c else ∅) addr := by rw [hW]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upFold_env_congr_fixed (E F : RAMEnv) (i c f : ℕ)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff)
    (hWord : E.det (1 % 2 ^ E.W) = F.det (1 % 2 ^ E.W))
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) :
    ∀ L : List UpIt, (∀ it ∈ L, it.setSt = 0) →
      (∀ it ∈ L, ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) →
        UpDetReadEq E F i it ⟨mem, c, f⟩) →
      ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) →
        upFold E i ⟨mem, c, f⟩ L = upFold F i ⟨mem, c, f⟩ L := by
  intro L
  induction L with
  | nil => intro hSet hRead mem hm; rfl
  | cons it L ih =>
      intro hSet hRead mem hm
      have hst := hSet it (by simp)
      have hq := hRead it (by simp) mem hm
      have happly := upApply_env_congr E F i it ⟨mem, c, f⟩ hW hPerm hCoef hWord hq.1 hq.2
      have hc' : (upApply E i it ⟨mem, c, f⟩).c = c := by
        change upvCnf E i it ⟨mem, c, f⟩ = c
        rw [upvCnf_of_setSt0 E i it _ hst]
        exact upvCn_of_setSt0 E i it _ hst hc
      have hf' : (upApply E i it ⟨mem, c, f⟩).f = f := by
        change upvFnf E i it ⟨mem, c, f⟩ = f
        rw [upvFnf_of_setSt0 E i it _ hst]
        exact upvFn_of_setSt0 E i it _ hst hf
      have he := upAbs_eta_coords (upApply E i it ⟨mem, c, f⟩) c f hc' hf'
      change upFold E i (upApply E i it ⟨mem, c, f⟩) L = upFold F i (upApply F i it ⟨mem, c, f⟩) L
      rw [← happly, he]
      apply ih (fun u hu => hSet u (List.mem_cons_of_mem _ hu))
        (fun u hu mem hm => hRead u (List.mem_cons_of_mem _ hu) mem hm)
      exact upApply_mem_bound E i it ⟨mem, c, f⟩ hm
theorem upIdle_reads_agree (E F : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs)
    (hW : 1 < 2 ^ E.W) (hStride : it.stride = 0) (hCidx : it.cidx = 0) (hSav : it.sav = 0)
    (h0 : E.det 0 = F.det 0) (h1 : E.det 1 = F.det 1) : UpDetReadEq E F i it a := by
  have ht : upvTb E i it a = 0 := by
    simp only [upvTb, upvX3, hStride, hCidx, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
  have hx : upvX5 E i it a = 1 := by
    simp only [upvX5, upvX4, ht, hSav, Nat.zero_add, Nat.zero_mod, Nat.mod_eq_of_lt hW]
  exact ⟨by rw [ht]; exact h0, by rw [hx]; exact h1⟩
theorem upCr_reads_agree (E F : RAMEnv) (i c f N Bc cidx base j : ℕ) (mem : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hcN : c < N) (hj : j < Bc)
    (hEnd : cidx + N * (Bc + 1) < 2 ^ E.W)
    (hAgree : ∀ a, cidx ≤ a → a < cidx + N * (Bc + 1) → E.det a = F.det a) :
    UpDetReadEq E F i (upCrIt cidx (Bc + 1) base j) ⟨mem, c, f⟩ := by
  have hrow := Nat.mul_le_mul_right (Bc + 1) (Nat.succ_le_of_lt hcN)
  have hnext : (Bc + 1) * c + cidx + (Bc + 1) ≤ cidx + N * (Bc + 1) := by
    nlinarith only [hrow]
  have hAddr : (Bc + 1) * c + cidx < 2 ^ E.W := by omega
  have hProd : (Bc + 1) * c < 2 ^ E.W := by omega
  have hElemAddr : (Bc + 1) * c + cidx + j + 1 < 2 ^ E.W := by omega
  have hCn := upvCn_of_setSt0 E i (upCrIt cidx (Bc + 1) base j) ⟨mem, c, f⟩ rfl hc
  have ht : upvTb E i (upCrIt cidx (Bc + 1) base j) ⟨mem, c, f⟩ = (Bc + 1) * c + cidx := by
    rw [upvTb, upvX3, hCn]
    change (((Bc + 1) * c) % 2 ^ E.W + cidx) % 2 ^ E.W = _
    rw [Nat.mod_eq_of_lt hProd, Nat.mod_eq_of_lt hAddr]
  have hx : upvX5 E i (upCrIt cidx (Bc + 1) base j) ⟨mem, c, f⟩ = (Bc + 1) * c + cidx + j + 1 := by
    rw [upvX5, upvX4, ht]
    change (((Bc + 1) * c + cidx + j) % 2 ^ E.W + 1 % 2 ^ E.W) % 2 ^ E.W = _
    rw [Nat.mod_eq_of_lt (by omega : (Bc + 1) * c + cidx + j < 2 ^ E.W),
      Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hElemAddr]
  exact ⟨by rw [ht]; exact hAgree _ (by omega) (by omega),
    by rw [hx]; exact hAgree _ (by omega) (by omega)⟩
theorem upOwnItems_reads_agree (CR : CRFamily) (E F : RAMEnv) (i Bc colBase : ℕ)
    (T : Node) (k base toff c f : ℕ) (hW : 1 < 2 ^ E.W)
    (hc : c < 2 ^ E.W) (hcN : c < T.N)
    (h0 : E.det 0 = F.det 0) (h1 : E.det 1 = F.det 1)
    (hEnd : colBase + toff + upTabLen Bc T < 2 ^ E.W)
    (hAgree : ∀ a, colBase + toff ≤ a → a < colBase + toff + upTabLen Bc T → E.det a = F.det a) :
    ∀ it ∈ upOwnItems CR Bc colBase T k base toff, ∀ mem : ℕ → ℕ,
      UpDetReadEq E F i it ⟨mem, c, f⟩ := by
  cases T with
  | store N =>
      intro it hi mem
      rw [upOwnItems, List.mem_singleton] at hi
      subst it
      exact upIdle_reads_agree E F i _ _ hW rfl rfl rfl h0 h1
  | cr N t =>
      intro it hi mem
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact upCr_reads_agree E F i c f N Bc (colBase + toff) base j mem hW hc hcN
        (List.mem_range.mp hj) hEnd hAgree
  | direct sch t =>
      intro it hi mem
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
        exact upIdle_reads_agree E F i _ _ hW rfl rfl rfl h0 h1
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact upCr_reads_agree E F i c f sch.N Bc (colBase + toff) _ j mem hW hc hcN
          (List.mem_range.mp hj) hEnd hAgree
  | recursive sch t Xs Ys child =>
      intro it hi mem
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      apply upCr_reads_agree E F i c f sch.N Bc (colBase + toff) _ j mem hW hc hcN
        (List.mem_range.mp hj)
      · simp only [upTabLen] at hEnd
        omega
      · intro a ha hb
        apply hAgree a ha
        change a < colBase + toff + (sch.N * (Bc + 1) + ∑ s, upTabLen Bc (child s))
        omega
theorem UpLocalBitsCorrect.of_table_extension (CR : CRFamily) (E F : RAMEnv) (i Bc colBase : ℕ)
    (T : Node) (r : T.Seed) (k base toff : ℕ)
    (hEW : 1 < 2 ^ E.W) (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff)
    (h0 : E.det 0 = F.det 0) (h1 : E.det 1 = F.det 1)
    (hEnd : colBase + toff + upTabLen Bc T < 2 ^ E.W)
    (hAgree : ∀ a, colBase + toff ≤ a → a < colBase + toff + upTabLen Bc T → E.det a = F.det a)
    (hOld : UpLocalBitsCorrect CR F i Bc colBase T r k base toff) :
    UpLocalBitsCorrect CR E i Bc colBase T r k base toff := by
  intro c f hcN hc hf hf01 mem hm addr
  have hWord : E.det (1 % 2 ^ E.W) = F.det (1 % 2 ^ E.W) := by rw [Nat.mod_eq_of_lt hEW]; exact h1
  have hrun := upFold_env_congr_fixed E F i c f hW hPerm hCoef hWord hc hf
    (upOwnItems CR Bc colBase T k base toff)
    (fun it hi => (upOwnItems_setSt0 CR Bc colBase T k base toff it hi).1)
    (fun it hi mem hm => upOwnItems_reads_agree CR E F i Bc colBase T k base toff c f
      hEW hc hcN h0 h1 hEnd hAgree it hi mem) mem hm
  have hcF : c < 2 ^ F.W := by rw [← hW]; exact hc
  have hfF : f < 2 ^ F.W := by rw [← hW]; exact hf
  have hmF : ∀ a, mem a < 2 ^ F.W := by intro a; rw [← hW]; exact hm a
  calc
    (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff)).mem addr =
      (upFold F i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff)).mem addr :=
        congrArg (fun a : UpAbs => a.mem addr) hrun
    _ = mem addr ^^^ packSel F.W (if f = 1 then upNodeLocalBits CR T r base c else ∅) addr :=
      hOld c f hcN hcF hfF hf01 mem hmF addr
    _ = mem addr ^^^ packSel E.W (if f = 1 then upNodeLocalBits CR T r base c else ∅) addr := by rw [hW]
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
def decItZero : DecIt := {}
def decDet (up : ℕ → ℕ) (hdr : ℕ → ℕ) (recOff : ℕ) (items : List DecIt) : ℕ → ℕ :=
  fun a =>
    if a = 3 then recOff
    else if a < recOff then up a
    else if a < recOff + 16 then hdr (a - recOff)
    else (items.getD ((a - recOff - 16) / 16) decItZero).fld ((a - recOff - 16) % 16)
theorem decDet_agrees (up hdr : ℕ → ℕ) (recOff : ℕ) (items : List DecIt) (a : ℕ)
    (ha : a < recOff) (h3 : a ≠ 3) : decDet up hdr recOff items a = up a := by
  unfold decDet
  rw [if_neg h3, if_pos ha]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def decAfterBase (colBase tabLen : ℕ) : ℕ := colBase + tabLen + 8
def decTabAfter (up hdr : ℕ → ℕ) (colBase tabLen : ℕ) (items : List DecIt) : ℕ → ℕ :=
  decDet up hdr (decAfterBase colBase tabLen) items
theorem decTabAfter_agrees (up hdr : ℕ → ℕ) (colBase tabLen : ℕ) (items : List DecIt) (a : ℕ)
    (ha : a < decAfterBase colBase tabLen) (h3 : a ≠ 3) :
    decTabAfter up hdr colBase tabLen items a = up a := decDet_agrees up hdr _ items a ha h3
theorem UpLocalBitsCorrect.of_decTabAfter (CR : CRFamily) (spec : TableSpec) (W : ℕ)
    (up hdr : ℕ → ℕ) (colBase tabLen : ℕ) (decItems : List DecIt) (rPublic : spec.Seed)
    (i Bc : ℕ) (T : Node) (rTree : T.Seed) (k base toff : ℕ)
    (hW : 1 < 2 ^ W) (hCol : 3 < colBase)
    (hSize : toff + upTabLen Bc T ≤ tabLen) (hEnd : colBase + tabLen < 2 ^ W)
    (hOld : UpLocalBitsCorrect CR (spec.env W up rPublic) i Bc colBase T rTree k base toff) :
    UpLocalBitsCorrect CR (spec.env W (decTabAfter up hdr colBase tabLen decItems) rPublic)
      i Bc colBase T rTree k base toff := by
  apply UpLocalBitsCorrect.of_table_extension CR
    (spec.env W (decTabAfter up hdr colBase tabLen decItems) rPublic) (spec.env W up rPublic)
    i Bc colBase T rTree k base toff hW rfl rfl rfl
  · change decTabAfter up hdr colBase tabLen decItems 0 = up 0
    exact decTabAfter_agrees up hdr colBase tabLen decItems 0 (by unfold decAfterBase; omega) (by decide)
  · change decTabAfter up hdr colBase tabLen decItems 1 = up 1
    exact decTabAfter_agrees up hdr colBase tabLen decItems 1 (by unfold decAfterBase; omega) (by decide)
  · change colBase + toff + upTabLen Bc T < 2 ^ W
    omega
  · intro a ha hb
    change decTabAfter up hdr colBase tabLen decItems a = up a
    exact decTabAfter_agrees up hdr colBase tabLen decItems a (by unfold decAfterBase; omega) (by omega)
  · exact hOld
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upCoin_env_congr (E F : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoef : E.coeff = F.coeff) :
    upvCoin E i it a = upvCoin F i it a := by
  have eq0 : upvZ1 E it a = upvZ1 F it a := by
    simp only [upvZ1, hW, hPerm]
  have eq1 : upvZ2 E i it = upvZ2 F i it := by
    simp only [upvZ2, hW]
  have eq2 : upvZ3 E it = upvZ3 F it := by
    simp only [upvZ3, hW]
  have eq3 : upvZ4 E it a = upvZ4 F it a := by
    simp only [upvZ4, eq0, eq2, hW]
  have eq4 : upvZ5 E i it a = upvZ5 F i it a := by
    simp only [upvZ5, eq1, eq3, hW]
  have eq5 : upvZ6 E it a = upvZ6 F it a := by
    simp only [upvZ6, hW]
  have eq6 : upvZ7 E it = upvZ7 F it := by
    simp only [upvZ7, hW]
  have eq7 : upvZ8 E i it a = upvZ8 F i it a := by
    simp only [upvZ8, eq4, eq6, hW]
  have eq8 : upvImg E i it a = upvImg F i it a := by
    simp only [upvImg, eq5, eq7, hW]
  have eq9 : upvJ0 E i it a = upvJ0 F i it a := by
    simp only [upvJ0, eq8, hW]
  have eq10 : upvPos E i it a = upvPos F i it a := by
    simp only [upvPos, eq8, hW]
  have eq11 : upvY1 E i it a = upvY1 F i it a := by
    simp only [upvY1, eq9, hW]
  have eq12 : upvY2 E i it a = upvY2 F i it a := by
    simp only [upvY2, eq11, hW]
  have eq13 : upvCn E i it a = upvCn F i it a := by
    simp only [upvCn, eq12, hW]
  have eq14 : upvY3 E i it a = upvY3 F i it a := by
    simp only [upvY3, eq9, hW]
  have eq15 : upvQ E i it a = upvQ F i it a := by
    simp only [upvQ, eq14, hW]
  have eq16 : upvY4 E i it a = upvY4 F i it a := by
    simp only [upvY4, eq15, hW]
  have eq17 : upvY5 E i it a = upvY5 F i it a := by
    simp only [upvY5, eq10, eq16, hW]
  have eq18 : upvCoin E i it a = upvCoin F i it a := by
    simp only [upvCoin, eq17, hW, hCoef]
  exact eq18
theorem UpEdgeData.of_env (E F : RAMEnv) (i k : ℕ) (sch : RowScheme) (lr : sch.LocalSeed)
    (s : Fin sch.ℓ) (c f : ℕ) (hW : E.W = F.W) (hPerm : E.perm = F.perm)
    (hCoef : E.coeff = F.coeff) (h : UpEdgeData E i k sch lr s c f) :
    UpEdgeData F i k sch lr s c f := by
  have hc := upCoin_env_congr E F i (upClimb k sch.m sch.ℓ (schemeNmax sch) s)
    ⟨fun _ => 0, c, f⟩ hW hPerm hCoef
  refine ⟨h.mpos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hW]; exact h.mword
  · rw [← hW, ← hPerm]; exact h.perm
  · rw [← hW, ← hPerm]; exact h.bit
  · dsimp only
    rw [← hc]
    exact h.coin
  · rw [← hc, ← hPerm]
    exact h.column
theorem UpLocalTree.of_decTabAfter (CR : CRFamily) (spec : TableSpec) (W : ℕ)
    (up hdr : ℕ → ℕ) (colBase tabLen : ℕ) (decItems : List DecIt) (rPublic : spec.Seed)
    (i Bc : ℕ) (hW : 1 < 2 ^ W) (hCol : 3 < colBase) (hEnd : colBase + tabLen < 2 ^ W) :
    ∀ (T : Node) (rTree : T.Seed) k base toff,
      toff + upTabLen Bc T ≤ tabLen →
      UpLocalTree CR (spec.env W up rPublic) i Bc colBase T rTree k base toff →
      UpLocalTree CR (spec.env W (decTabAfter up hdr colBase tabLen decItems) rPublic)
        i Bc colBase T rTree k base toff := by
  intro T
  induction T with
  | store N =>
      intro rTree k base toff hSize hOld
      exact UpLocalBitsCorrect.of_decTabAfter CR spec W up hdr colBase tabLen decItems rPublic
        i Bc (.store N) rTree k base toff hW hCol hSize hEnd hOld
  | cr N t =>
      intro rTree k base toff hSize hOld
      exact UpLocalBitsCorrect.of_decTabAfter CR spec W up hdr colBase tabLen decItems rPublic
        i Bc (.cr N t) rTree k base toff hW hCol hSize hEnd hOld
  | direct sch t =>
      intro rTree k base toff hSize hOld
      exact UpLocalBitsCorrect.of_decTabAfter CR spec W up hdr colBase tabLen decItems rPublic
        i Bc (.direct sch t) rTree k base toff hW hCol hSize hEnd hOld
  | recursive sch t Xs Ys child ih =>
      intro rTree k base toff hSize hOld
      refine ⟨?_, hOld.2.1, ?_, ?_⟩
      · exact UpLocalBitsCorrect.of_decTabAfter CR spec W up hdr colBase tabLen decItems rPublic
          i Bc (.recursive sch t Xs Ys child) rTree k base toff hW hCol hSize hEnd hOld.1
      · intro c f hcN hc hf hf01 s
        exact UpEdgeData.of_env (spec.env W up rPublic)
          (spec.env W (decTabAfter up hdr colBase tabLen decItems) rPublic)
          i k sch rTree.1 s c f rfl rfl rfl (hOld.2.2.1 c f hcN hc hf hf01 s)
      · intro s
        apply ih s (rTree.2 s) _ _ _ ?_ (hOld.2.2.2 s)
        have hTop : upKidOff Bc sch child toff s.val + upTabLen Bc (child s) ≤
            toff + upTabLen Bc (.recursive sch t Xs Ys child) :=
          upKidOff_le_top Bc sch child toff s.val s.isLt
        exact hTop.trans hSize
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false



#print axioms LinearSetReconciliation327.Main.upRoot_layout_fits
#print axioms LinearSetReconciliation327.Main.upRoot_localTree


