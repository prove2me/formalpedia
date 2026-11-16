-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:20:25.967993+00:00
-- url     : https://prove2.me/theorems/39fa18e7-f1b0-4ecf-90e8-ad7807469d8d
-- title:
--   Block-0 low-slot leaf-mix state
-- statement:
--   # Block-0 low-slot leaf-mix state
--
--   Evaluation of the leaf-mix generator on low slots: for each leaf index $t$ and each slot $q$ in the interval of leaf $t$, the generated state at the corresponding auxiliary wire equals the source code $cND t$. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   Depends on the published `Block0CoreAData`, `Block0CoreABits`, `Block0CoreACopy`, `Block0CoreALeaf`, and `Block0CoreAState1` packs.
--
--   ## Formalization Note
--
--   Lean identifiers: `leafMix_state_low`, `leafMixOf_low`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA State2 split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
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
Block-0 low-slot leafMix state (`leafMixOf_low` / `leafMix_state_low`).
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem leafMixOf_low (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hP : ∀ t ∈ ts, f (wS (srcS t)) = cND t)
    (hE : ∀ t ∈ ts, ∀ o ∈ leafExtras t, f (wS o) = 0)
    (hDone : ∀ t, t < v → t ∉ ts → ∀ q, srcS t ≤ q ∧ q < leafHi t → f (wS q) = cND t)
    {t q : ℕ} (ht : t < v) (hin : srcS t ≤ q ∧ q < leafHi t) :
    (genF f (ts.map leafAt)).1 (wS q) = cND t := by
  induction ts generalizing f with
  | nil =>
    have hnin : t ∉ ([] : List ℕ) := List.not_mem_nil
    exact hDone t ht hnin q hin
  | cons t0 ts ih =>
    have hcons := List.nodup_cons.1 hnd
    have ht0nin : t0 ∉ ts := hcons.1
    have hnd' : ts.Nodup := hcons.2
    have ht0 : t0 < v := htv t0 (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have happ := genF_append f [leafAt t0] (ts.map leafAt)
    simp only [List.singleton_append] at happ
    have hmap : (t0 :: ts).map leafAt = leafAt t0 :: ts.map leafAt := rfl
    rw [hmap, happ]
    set f' := (genF f [leafAt t0]).1
    have hgen := genF_singleton f (leafAt t0)
    have hP' : ∀ t' ∈ ts, f' (wS (srcS t')) = cND t' := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne : t' ≠ t0 := by intro heq; subst heq; exact ht0nin ht'
      have hnt := not_mem_leafAt_touch_srcS ht0 ht'v hne.symm
      have : f' (wS (srcS t')) = f (wS (srcS t')) := by
        unfold f'; rw [hgen, leafAt_code]
        exact foldl_mvF_untouched (cND t0) (leafAt t0).2.1 f [] hnt
      rw [this]
      exact hP t' (List.mem_cons_of_mem _ ht')
    have hE' : ∀ t' ∈ ts, ∀ o ∈ leafExtras t', f' (wS o) = 0 := by
      intro t' ht' o ho
      have ht'v : t' < v := htv' t' ht'
      have hne : t' ≠ t0 := by intro heq; subst heq; exact ht0nin ht'
      have hnt := not_mem_leafAt_touch_extra ht0 ht'v hne.symm ho
      have : f' (wS o) = f (wS o) := by
        unfold f'; rw [hgen, leafAt_code]
        exact foldl_mvF_untouched (cND t0) (leafAt t0).2.1 f [] hnt
      rw [this]
      exact hE t' (List.mem_cons_of_mem _ ht') o ho
    have hDone' : ∀ t', t' < v → t' ∉ ts → ∀ q', srcS t' ≤ q' ∧ q' < leafHi t' →
        f' (wS q') = cND t' := by
      intro t' ht' hnin q' hin'
      by_cases hteq : t' = t0
      · have hf'eq : f' = (genF f [leafAt t']).1 := by
          unfold f'; rw [hteq]
        have hgen' := genF_singleton f (leafAt t')
        have hmem := (mem_leaf_interval ht').1 hin'
        have hcode : (leafAt t').1 = cND t' := leafAt_code t'
        rcases hmem with hpiv | hex
        · have hpiv' : q' = srcS t' := hpiv
          rw [hpiv']
          by_cases htouch : wS (srcS t') ∈ (leafAt t').2.1
          · have : f' (wS (srcS t')) = cND t' := by
              rw [hf'eq, hgen', hcode]
              exact foldl_mvF_written (cND t') (leafAt t').2.1 f [] htouch
            exact this
          · have : f' (wS (srcS t')) = f (wS (srcS t')) := by
              rw [hf'eq, hgen', hcode]
              exact foldl_mvF_untouched (cND t') (leafAt t').2.1 f [] htouch
            exact this.trans (hP t' (List.mem_cons.2 (Or.inl hteq)))
        · have htouch : wS q' ∈ (leafAt t').2.1 := by
            rw [leafAt_touch]
            refine List.mem_flatMap.2 ⟨q', hex, ?_⟩
            simp
          have : f' (wS q') = cND t' := by
            rw [hf'eq, hgen', hcode]
            exact foldl_mvF_written (cND t') (leafAt t').2.1 f [] htouch
          exact this
      · have hnin0 : t' ∉ t0 :: ts := by
          intro hmem
          rcases List.mem_cons.1 hmem with h | h
          · exact hteq h
          · exact hnin h
        have hne : t0 ≠ t' := fun h => hteq h.symm
        have hstay : f' (wS q') = f (wS q') := by
          have hnt : wS q' ∉ (leafAt t0).2.1 := by
            have hmem := (mem_leaf_interval ht').1 hin'
            rcases hmem with hpiv | hex
            · have : q' = srcS t' := hpiv
              rw [this]
              exact not_mem_leafAt_touch_srcS ht0 ht' hne
            · exact not_mem_leafAt_touch_extra ht0 ht' hne hex
          unfold f'; rw [hgen, leafAt_code]
          exact foldl_mvF_untouched (cND t0) (leafAt t0).2.1 f [] hnt
        exact hstay.trans (hDone t' ht' hnin0 q' hin')
    exact ih f' hnd' htv' hP' hE' hDone'


theorem leafMix_state_low (f : ℕ → ℕ)
    (hP : ∀ t, t < v → f (wS (srcS t)) = cND t)
    (hE : ∀ t, t < v → ∀ o ∈ leafExtras t, f (wS o) = 0)
    {t q : ℕ} (ht : t < v) (hin : srcS t ≤ q ∧ q < leafHi t) :
    (genF f leafMix).1 (wS q) = cND t := by
  have H : ∀ n, n = v → (genF f (leafMixOf n)).1 (wS q) = cND t := by
    intro n hn
    refine leafMixOf_low f (List.range n) List.nodup_range
      (fun t ht => Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
      (fun t ht => hP t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      (fun t ht => hE t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      ?_ ht hin
    intro t' ht' hnin q' hin'
    have : t' ∈ List.range n := List.mem_range.2 (Nat.lt_of_lt_of_eq ht' hn.symm)
    exact (hnin this).elim
  unfold leafMix
  exact H v rfl


