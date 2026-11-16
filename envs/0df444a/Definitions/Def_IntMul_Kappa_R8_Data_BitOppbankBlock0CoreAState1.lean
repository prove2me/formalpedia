-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:15:16.279207+00:00
-- url     : https://prove2.me/theorems/0e0ab6af-9cad-4fb6-a578-506cb2f6ca82
-- title:
--   Block-0 high-slot leaf-mix state and leaf owners
-- statement:
--   # Block-0 high-slot leaf-mix state
--
--   Existence of a unique leaf owner for each slot below the leaf-slot bound, together with the evaluation of the leaf-mix generator on high slots (those at or above the leaf-slot bound). Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   Depends on the published `Block0CoreAData`, `Block0CoreABits`, `Block0CoreACopy`, and `Block0CoreALeaf` packs.
--
--   ## Formalization Note
--
--   Lean identifiers: `exists_leaf_owner`, `leafMix_state_high`, `leafMixOf_high`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA State1 split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 high-slot leafMix state and leaf-owner existence.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem srcS_zero : srcS 0 = 0 := by
  have h0 : (0 : ℕ) < v := by decide
  rw [srcS_get h0]
  rfl

theorem foldl_mvF_written (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ) (acc : List (ℕ × ℕ))
    {x : ℕ} (hx : x ∈ ws) :
    (ws.foldl (mvF c) (f, acc)).1 x = c := by
  induction ws generalizing f acc with
  | nil => cases hx
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with h | h
    · have hxw : x = w := h
      by_cases hfw : f w = c
      · have : mvF c (f, acc) w = (f, acc) := by simp [mvF, hfw]
        rw [this]
        by_cases hw' : w ∈ ws
        · exact ih f acc (by simpa [hxw] using hw')
        · have hxnin : x ∉ ws := by simpa [hxw] using hw'
          have hun := foldl_mvF_untouched c ws f acc hxnin
          rw [hun, hxw]
          exact hfw
      · have : mvF c (f, acc) w =
          (fun y => if y = w then c else f y, (w, f w) :: acc) := by
          simp [mvF, hfw]
        rw [this]
        by_cases hw' : w ∈ ws
        · exact ih (fun y => if y = w then c else f y) ((w, f w) :: acc)
            (by simpa [hxw] using hw')
        · have hxnin : x ∉ ws := by simpa [hxw] using hw'
          have hnt := foldl_mvF_untouched c ws (fun y => if y = w then c else f y)
            ((w, f w) :: acc) hxnin
          simpa [hxw] using hnt
    · by_cases hfw : f w = c
      · have : mvF c (f, acc) w = (f, acc) := by simp [mvF, hfw]
        rw [this]
        exact ih f acc h
      · have : mvF c (f, acc) w =
          (fun y => if y = w then c else f y, (w, f w) :: acc) := by
          simp [mvF, hfw]
        rw [this]
        exact ih (fun y => if y = w then c else f y) ((w, f w) :: acc) h




theorem exists_leaf_owner {q : ℕ} (hq : q < leafSlotBound) :
    ∃ t, t < v ∧ srcS t ≤ q ∧ q < leafHi t := by
  have hstart : srcS 0 ≤ q := by
    rw [srcS_zero]; exact Nat.zero_le q
  have hex : ∃ t, t < v ∧ srcS t ≤ q ∧ ∀ t' < v, srcS t' ≤ q → t' ≤ t := by
    have hfin : (⟨0, by decide⟩ : Fin v) = ⟨0, by decide⟩ := rfl
    let s : Finset (Fin v) := Finset.univ.filter (fun t => srcS t.val ≤ q)
    have hsne : s.Nonempty := by
      refine ⟨⟨0, by decide⟩, ?_⟩
      simp [s, hstart]
    refine ⟨(s.max' hsne).val, (s.max' hsne).isLt, ?_, ?_⟩
    · have : s.max' hsne ∈ s := Finset.max'_mem _ hsne
      exact (Finset.mem_filter.1 this).2
    · intro t' ht' hle
      have htF : (⟨t', ht'⟩ : Fin v) ∈ s := by
        simp [s, hle]
      exact Fin.val_le_of_le (Finset.le_max' s _ htF)
  rcases hex with ⟨t, ht, hle, hmax⟩
  refine ⟨t, ht, hle, ?_⟩
  unfold leafHi
  split_ifs with hv
  · exact hq
  · have ht1 : t + 1 < v := srcS_succ_lt_of_ne ht hv
    have : ¬ srcS (t + 1) ≤ q := fun h =>
      Nat.not_succ_le_self t (hmax (t + 1) ht1 h)
    exact Nat.not_le.mp this



theorem not_mem_leafAt_touch_high {t q : ℕ} (ht : t < v) (hq : leafSlotBound ≤ q) :
    wS q ∉ (leafAt t).2.1 := by
  rw [leafAt_touch]
  intro hx
  rcases List.mem_flatMap.1 hx with ⟨o, ho, hx'⟩
  have hcases : wS q = wS o ∨ wS q = wS (srcS t) := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx'
    exact hx'
  have hqo : q ≠ o := by
    have : o < leafHi t := (mem_leafExtras ht).1 ho |>.2
    have : o < leafSlotBound := Nat.lt_of_lt_of_le this (leafHi_le_slotBound ht)
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le this hq)
  have hqs : q ≠ srcS t := by
    have : srcS t < 11091 := srcS_lt ht
    have : srcS t < leafSlotBound := Nat.lt_trans this (by decide)
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le this hq)
  rcases hcases with h | h
  · exact hqo (wS_inj h)
  · exact hqs (wS_inj h)


theorem leafMixOf_high (f : ℕ → ℕ) (ts : List ℕ)
    (htv : ∀ t ∈ ts, t < v)
    (hHigh : ∀ q, leafSlotBound ≤ q → wS q < wAuxEnd → f (wS q) = 0)
    {q : ℕ} (hq : leafSlotBound ≤ q) (hqw : wS q < wAuxEnd) :
    (genF f (ts.map leafAt)).1 (wS q) = 0 := by
  induction ts generalizing f with
  | nil =>
    simp [genF]; exact hHigh q hq hqw
  | cons t ts ih =>
    have ht : t < v := htv t (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have happ := genF_append f [leafAt t] (ts.map leafAt)
    simp only [List.singleton_append] at happ
    have hmap : (t :: ts).map leafAt = leafAt t :: ts.map leafAt := rfl
    rw [hmap, happ]
    set f' := (genF f [leafAt t]).1
    have hf' : f' (wS q) = f (wS q) := by
      have hgen := genF_singleton f (leafAt t)
      unfold f'
      rw [hgen, leafAt_code]
      exact foldl_mvF_untouched (cND t) (leafAt t).2.1 f [] (not_mem_leafAt_touch_high ht hq)
    have hHigh' : ∀ q', leafSlotBound ≤ q' → wS q' < wAuxEnd → f' (wS q') = 0 := by
      intro q' hq' hqw'
      have hgen := genF_singleton f (leafAt t)
      have : f' (wS q') = f (wS q') := by
        unfold f'
        rw [hgen, leafAt_code]
        exact foldl_mvF_untouched (cND t) (leafAt t).2.1 f [] (not_mem_leafAt_touch_high ht hq')
      rw [this]
      exact hHigh q' hq' hqw'
    exact ih f' htv' hHigh'


theorem leafMix_state_high (f : ℕ → ℕ)
    (hHigh : ∀ q, leafSlotBound ≤ q → wS q < wAuxEnd → f (wS q) = 0)
    {q : ℕ} (hq : leafSlotBound ≤ q) (hqw : wS q < wAuxEnd) :
    (genF f leafMix).1 (wS q) = 0 := by
  have H : ∀ n, n = v → (genF f (leafMixOf n)).1 (wS q) = 0 := by
    intro n hn
    refine leafMixOf_high f (List.range n)
      (fun t ht => Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn) hHigh hq hqw
  unfold leafMix
  exact H v rfl



theorem mem_leaf_interval {t q : ℕ} (ht : t < v) :
    srcS t ≤ q ∧ q < leafHi t ↔ q = srcS t ∨ q ∈ leafExtras t := by
  constructor
  · intro ⟨hle, hhi⟩
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((mem_leafExtras ht).2 ⟨h, hhi⟩)
  · intro h
    rcases h with h | h
    · subst h
      exact ⟨Nat.le_refl _, Nat.lt_of_succ_le (srcS_lt_leafHi ht)⟩
    · have ⟨hlo, hhi⟩ := (mem_leafExtras ht).1 h
      exact ⟨Nat.le_of_lt hlo, hhi⟩


