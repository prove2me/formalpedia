-- Prove2me | Definitions.Def_GirvingAKS_Sort_Monotone
-- name    : GirvingAKS_Sort_Monotone
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:26.884894+00:00
-- url     : https://prove2.me/theorems/55b32aec-cc65-472f-ab87-253eff600da3
-- title:
--   AKS sorting networks (Seiferas port) — Monotonicity Preservation for Comparator Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Monotone.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Comparators and networks preserve monotonicity of input functions. This is the key structural property underlying the 0-1 principle.
--
--   Main results:
--
--   - `Comparator.apply_comp_monotone`: monotone functions commute with comparator application
--   - `Comparator.apply_preserves_monotone`: comparators preserve monotone inputs
--   - `ComparatorNetwork.exec_comp_monotone`: monotone functions commute with network execution
--   - `ComparatorNetwork.Sorts`: a network sorts all inputs iff every output is monotone
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Monotone.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Monotone.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Monotonicity Preservation for Comparator Networks

  Comparators and networks preserve monotonicity of input functions.
  This is the key structural property underlying the 0-1 principle.

  Main results:
  • `Comparator.apply_comp_monotone`: monotone functions commute with comparator application
  • `Comparator.apply_preserves_monotone`: comparators preserve monotone inputs
  • `ComparatorNetwork.exec_comp_monotone`: monotone functions commute with network execution
  • `ComparatorNetwork.Sorts`: a network sorts all inputs iff every output is monotone
-/


section


open Finset BigOperators


/-! **Helper Lemmas** -/

/-- For comparator positions i < j, monotone w gives w i ≤ w j -/
private lemma Comparator.monotone_at_positions {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {w : Fin n → α} (hw : Monotone w) :
    w c.i ≤ w c.j :=
  hw (Fin.le_of_lt c.h)


/-! **Comparator Preservation Lemmas** -/

/-- Monotone functions commute with a single comparator application.
    This is the key lemma for the 0-1 principle: min/max commute
    with monotone functions on linear orders. -/
theorem Comparator.apply_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (c : Comparator n) {f : α → β} (hf : Monotone f) (v : Fin n → α) :
    f ∘ c.apply v = c.apply (f ∘ v) := by
  ext k
  simp only [Function.comp, Comparator.apply]
  split_ifs with h1 h2
  · exact hf.map_min
  · exact hf.map_max
  · rfl

/-- Comparators preserve monotonicity: if w is monotone, then c.apply w is monotone -/
theorem Comparator.apply_preserves_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (hw : Monotone w) :
    Monotone (c.apply w) := by
  intro a b hab
  unfold Comparator.apply
  -- Case split on whether a, b are among {c.i, c.j}
  by_cases ha_i : a = c.i
  · -- Case: a = c.i
    rw [if_pos ha_i]
    by_cases hb_i : b = c.i
    · -- Subcase: b = c.i
      rw [if_pos hb_i]
    · -- Subcase: b ≠ c.i
      rw [if_neg hb_i]
      by_cases hb_j : b = c.j
      · -- b = c.j
        rw [if_pos hb_j]
        exact min_le_max
      · -- b ∉ {c.i, c.j}
        rw [if_neg hb_j]
        have : c.i ≤ b := ha_i ▸ hab
        have : c.i < b := Fin.lt_of_le_of_ne this (Ne.symm hb_i)
        exact le_trans (min_le_left _ _) (hw (Fin.le_of_lt this))
  · -- Case: a ≠ c.i
    rw [if_neg ha_i]
    by_cases ha_j : a = c.j
    · -- a = c.j
      rw [if_pos ha_j]
      by_cases hb_i : b = c.i
      · -- This case is impossible: a = c.j ≤ b = c.i, but c.i < c.j
        exfalso
        have : c.j ≤ c.i := by rw [← hb_i]; exact ha_j ▸ hab
        exact absurd c.h (not_lt.mpr this)
      · rw [if_neg hb_i]
        by_cases hb_j : b = c.j
        · -- b = c.j
          rw [if_pos hb_j]
        · -- b ≠ c.j
          rw [if_neg hb_j]
          have : c.j ≤ b := ha_j ▸ hab
          have : c.j < b := Fin.lt_of_le_of_ne this (Ne.symm hb_j)
          have : w c.i ≤ w c.j := c.monotone_at_positions hw
          calc max (w c.i) (w c.j) = w c.j := max_eq_right this
            _ ≤ w b := hw (Fin.le_of_lt ‹c.j < b›)
    · -- a ∉ {c.i, c.j}
      rw [if_neg ha_j]
      by_cases hb_i : b = c.i
      · -- b = c.i
        rw [if_pos hb_i]
        have : a ≤ c.i := hb_i ▸ hab
        have : a < c.i := Fin.lt_of_le_of_ne this ha_i
        have : a < c.j := Nat.lt_trans this c.h
        exact le_min (hw (Fin.le_of_lt ‹a < c.i›)) (hw (Fin.le_of_lt ‹a < c.j›))
      · rw [if_neg hb_i]
        by_cases hb_j : b = c.j
        · -- b = c.j
          rw [if_pos hb_j]
          have : a ≤ c.j := hb_j ▸ hab
          have : a < c.j := Fin.lt_of_le_of_ne this ha_j
          by_cases hai : a < c.i
          · exact le_trans (hw (Fin.le_of_lt hai)) (le_max_left _ _)
          · push_neg at hai
            exact le_trans (hw (Fin.le_of_lt ‹a < c.j›)) (le_max_right _ _)
        · -- b ∉ {c.i, c.j}
          rw [if_neg hb_j]
          exact hw hab

/-- Network execution preserves monotonicity: if w is monotone, then net.exec w is monotone -/
theorem ComparatorNetwork.exec_preserves_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (w : Fin n → α) (hw : Monotone w) :
    Monotone (net.exec w) := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => exact hw
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (c.apply w) (c.apply_preserves_monotone w hw)

/-- Monotone functions commute with sequential comparator application. -/
private theorem foldl_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (cs : List (Comparator n)) {f : α → β} (hf : Monotone f)
    (v : Fin n → α) :
    f ∘ cs.foldl (fun acc c ↦ c.apply acc) v =
      cs.foldl (fun acc c ↦ c.apply acc) (f ∘ v) := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (c.apply v), c.apply_comp_monotone hf v]

/-- Monotone functions commute with network execution.
    Extends `apply_comp_monotone` to the full comparator sequence. -/
theorem ComparatorNetwork.exec_comp_monotone {n : ℕ} {α β : Type*}
    [LinearOrder α] [LinearOrder β]
    (net : ComparatorNetwork n) {f : α → β} (hf : Monotone f)
    (v : Fin n → α) :
    f ∘ net.exec v = net.exec (f ∘ v) :=
  foldl_comp_monotone net.comparators hf v

/-- A comparator applied to a monotone function is the identity:
    `v(c.i) ≤ v(c.j)` already holds, so `min = v(c.i)` and `max = v(c.j)`. -/
theorem Comparator.apply_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {v : Fin n → α} (hv : Monotone v) :
    c.apply v = v := by
  ext k; unfold Comparator.apply
  by_cases hki : k = c.i
  · subst hki; rw [if_pos rfl, min_eq_left (hv (Fin.le_of_lt c.h))]
  · rw [if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj; rw [if_pos rfl, max_eq_right (hv (Fin.le_of_lt c.h))]
    · rw [if_neg hkj]

/-- Network execution on a monotone input is the identity: already-sorted
    inputs are not modified by any comparator. -/
theorem ComparatorNetwork.exec_eq_of_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Monotone v) :
    net.exec v = v := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [c.apply_eq_of_monotone hv]
    exact ih hv

/-- A network is a *sorting network* if it sorts every input. -/
def ComparatorNetwork.Sorts {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (α : Type*) [LinearOrder α] (v : Fin n → α),
    Monotone (net.exec v)

end


