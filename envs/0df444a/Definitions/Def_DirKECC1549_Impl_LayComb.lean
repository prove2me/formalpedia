-- Prove2me | Definitions.Def_DirKECC1549_Impl_LayComb
-- name    : DirKECC1549_Impl_LayComb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T03:03:00.920206+00:00
-- url     : https://prove2.me/theorems/0b6dbf25-a637-47e1-affd-ab1f3f470e4a
-- title:
--   Counting sort: counts, positions and the sorting permutation
-- statement:
--   The counting notions $\#\{e:\kappa(e)<v\}$, $\#\{e:\kappa(e)=v\}$, $\#\{e<j:\kappa(e)=v\}$, the counting-sort position `posK` and the sorting permutation `sortPerm`.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Mathlib

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

variable {m : ℕ}

/-- `#{e : key e < v}`. -/
def cntLT (key : Fin m → ℕ) (v : ℕ) : ℕ := (univ.filter (fun e => key e < v)).card
/-- `#{e : key e = v}`. -/
def cntEQ (key : Fin m → ℕ) (v : ℕ) : ℕ := (univ.filter (fun e => key e = v)).card
/-- `#{e < j : key e = v}`. -/
def cntEQb (key : Fin m → ℕ) (j v : ℕ) : ℕ :=
  (univ.filter (fun e : Fin m => (e : ℕ) < j ∧ key e = v)).card
/-- The position of `e` after a stable counting sort by `key`. -/
def posK (key : Fin m → ℕ) (e : Fin m) : ℕ := cntLT key (key e) + cntEQb key e (key e)

theorem cntLT_le (key : Fin m → ℕ) (v : ℕ) : cntLT key v ≤ m := by
  unfold cntLT; exact le_trans (card_filter_le _ _) (by simp)

theorem cntLT_mono (key : Fin m → ℕ) {v v' : ℕ} (h : v ≤ v') : cntLT key v ≤ cntLT key v' := by
  unfold cntLT; exact card_le_card (fun e => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem cntLT_succ (key : Fin m → ℕ) (v : ℕ) : cntLT key (v + 1) = cntLT key v + cntEQ key v := by
  unfold cntLT cntEQ
  rw [← card_union_of_disjoint (disjoint_filter.2 (fun e _ h1 h2 => by omega))]
  congr 1; ext e; simp only [mem_filter, mem_univ, true_and, mem_union]; omega

theorem cntEQb_lt (key : Fin m → ℕ) (e : Fin m) : cntEQb key e (key e) < cntEQ key (key e) := by
  unfold cntEQb cntEQ
  apply card_lt_card
  refine ⟨fun x => by simp only [mem_filter, mem_univ, true_and]; tauto, fun h => ?_⟩
  have := h (show e ∈ univ.filter (fun x => key x = key e) by simp)
  simp at this

theorem cntEQb_strict (key : Fin m → ℕ) {e e' : Fin m} (hk : key e = key e') (h : e < e') :
    cntEQb key e (key e) < cntEQb key e' (key e') := by
  unfold cntEQb
  rw [← hk]
  apply card_lt_card
  refine ⟨fun x => by
    simp only [mem_filter, mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨by have := Fin.lt_def.1 h; omega, h2⟩, fun hs => ?_⟩
  have := hs (show e ∈ univ.filter (fun x : Fin m => (x : ℕ) < e' ∧ key x = key e) by
    simp only [mem_filter, mem_univ, true_and]; exact ⟨Fin.lt_def.1 h, by trivial⟩)
  simp at this

theorem posK_lt (key : Fin m → ℕ) (e : Fin m) : posK key e < cntLT key (key e + 1) := by
  unfold posK; rw [cntLT_succ]; have := cntEQb_lt key e; omega

theorem posK_lt_m (key : Fin m → ℕ) (e : Fin m) : posK key e < m :=
  lt_of_lt_of_le (posK_lt key e) (cntLT_le key _)

theorem posK_ge (key : Fin m → ℕ) (e : Fin m) : cntLT key (key e) ≤ posK key e := by
  unfold posK; omega

theorem posK_inj (key : Fin m → ℕ) : Function.Injective (fun e : Fin m => (⟨posK key e, posK_lt_m key e⟩ : Fin m)) := by
  intro e e' h
  simp only [Fin.mk.injEq] at h
  by_contra hne
  rcases lt_trichotomy (key e) (key e') with hk | hk | hk
  · have h1 := posK_lt key e
    have h2 := posK_ge key e'
    have h3 := cntLT_mono key (show key e + 1 ≤ key e' by omega)
    omega
  · rcases lt_or_gt_of_ne hne with hl | hl
    · have := cntEQb_strict key hk hl; unfold posK at h; rw [hk] at h this; omega
    · have := cntEQb_strict key hk.symm hl; unfold posK at h; rw [hk] at h this; omega
  · have h1 := posK_lt key e'
    have h2 := posK_ge key e
    have h3 := cntLT_mono key (show key e' + 1 ≤ key e by omega)
    omega

/-- The permutation sorting by `key`: `σ (posK e) = e`. -/
noncomputable def sortPerm (key : Fin m → ℕ) : Equiv.Perm (Fin m) :=
  (Equiv.ofBijective _ ((posK_inj key).bijective_of_finite)).symm

end DirKECC1549.Asm


