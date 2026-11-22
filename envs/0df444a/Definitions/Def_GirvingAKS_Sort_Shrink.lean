-- Prove2me | Definitions.Def_GirvingAKS_Sort_Shrink
-- name    : GirvingAKS_Sort_Shrink
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:15.654823+00:00
-- url     : https://prove2.me/theorems/4f56b795-7164-4297-965a-deef88e31daf
-- title:
--   AKS sorting networks (Seiferas port) — Wire Restriction for Comparator Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Shrink.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Restrict a network from n wires to m ≤ n wires by keeping only comparators where both endpoints are in [0, m). This enables non-power-of-two sorting networks: build at 2^⌈log₂ n⌉ then restrict to n wires.
--
--   Main results:
--
--   - `ComparatorNetwork.restrictWires` — computable wire restriction
--   - `restrictWires_depth_le` — depth can only decrease
--   - `restrictWires_sorts` — sorting is preserved
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Shrink.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Monotone
import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Sort_ZeroOne

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Shrink.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Wire Restriction for Comparator Networks

  Restrict a network from n wires to m ≤ n wires by keeping only
  comparators where both endpoints are in [0, m). This enables
  non-power-of-two sorting networks: build at 2^⌈log₂ n⌉ then
  restrict to n wires.

  Main results:
  • `ComparatorNetwork.restrictWires` — computable wire restriction
  • `restrictWires_depth_le` — depth can only decrease
  • `restrictWires_sorts` — sorting is preserved
-/


section


/-! **Wire Restriction** -/

/-- The filter used by `restrictWires`: keep comparators with both endpoints in `[0, m)`. -/
def restrictFilter {n : ℕ} (m : ℕ) (c : Comparator n) : Option (Comparator m) :=
  if hi : c.i.val < m then
    if hj : c.j.val < m then
      some ⟨⟨c.i.val, hi⟩, ⟨c.j.val, hj⟩, by exact c.h⟩
    else none
  else none

/-- Restrict a network from `n` wires to `m ≤ n` wires by keeping only
    comparators where both endpoints are in `[0, m)`. -/
def ComparatorNetwork.restrictWires {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (_hm : m ≤ n) : ComparatorNetwork m :=
  ⟨net.comparators.filterMap (restrictFilter m)⟩

/-! **Depth bound** -/

/-- Depth invariant: restricted wire times ≤ original wire times at
    corresponding positions, and restricted running max ≤ original. -/
private lemma restrictWires_depth_foldl {n m : ℕ} (hm : m ≤ n)
    (cs : List (Comparator n))
    (wt_n : Fin n → ℕ) (dm_n : ℕ) (wt_m : Fin m → ℕ) (dm_m : ℕ)
    (hwt : ∀ i : Fin m, wt_m i ≤ wt_n ⟨i.val, by omega⟩)
    (hdm : dm_m ≤ dm_n) :
    (cs.filterMap (restrictFilter m) |>.foldl depthStep (wt_m, dm_m)).2 ≤
    (cs.foldl depthStep (wt_n, dm_n)).2 := by
  induction cs generalizing wt_n dm_n wt_m dm_m with
  | nil => simpa
  | cons c cs ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    unfold restrictFilter
    by_cases hi : c.i.val < m
    · by_cases hj : c.j.val < m
      · -- Both endpoints < m: comparator kept
        simp only [hi, hj, dite_true, List.foldl_cons]
        apply ih
        · -- Wire times invariant after one depthStep on each side
          intro k
          simp only [Function.update_apply]
          have h_ci := hwt ⟨c.i.val, hi⟩
          have h_cj := hwt ⟨c.j.val, hj⟩
          have hk := hwt k
          -- Case split on val equalities to align Fin m and Fin n branches
          by_cases hkj_val : k.val = c.j.val
          · have hkj_m : k = ⟨c.j.val, hj⟩ := Fin.ext hkj_val
            have hkj_n : (⟨k.val, by omega⟩ : Fin n) = c.j := Fin.ext hkj_val
            rw [if_pos hkj_m, if_pos hkj_n]
            exact Nat.add_le_add_right (Nat.max_le.mpr
              ⟨le_trans h_ci (le_max_left _ _), le_trans h_cj (le_max_right _ _)⟩) 1
          · have hkj_m : k ≠ ⟨c.j.val, hj⟩ := fun h => hkj_val (congr_arg Fin.val h)
            have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := fun h => hkj_val (congr_arg Fin.val h)
            rw [if_neg hkj_m, if_neg hkj_n]
            by_cases hki_val : k.val = c.i.val
            · have hki_m : k = ⟨c.i.val, hi⟩ := Fin.ext hki_val
              have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
              rw [if_pos hki_m, if_pos hki_n]
              exact Nat.add_le_add_right (Nat.max_le.mpr
                ⟨le_trans h_ci (le_max_left _ _), le_trans h_cj (le_max_right _ _)⟩) 1
            · have hki_m : k ≠ ⟨c.i.val, hi⟩ := fun h => hki_val (congr_arg Fin.val h)
              have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
              rw [if_neg hki_m, if_neg hki_n]
              exact hk
        · -- Running max invariant
          dsimp only []
          have h_ci := hwt ⟨c.i.val, hi⟩
          have h_cj := hwt ⟨c.j.val, hj⟩
          have : max (wt_m ⟨c.i.val, hi⟩) (wt_m ⟨c.j.val, hj⟩) ≤
              max (wt_n c.i) (wt_n c.j) :=
            Nat.max_le.mpr ⟨le_trans h_ci (le_max_left _ _), le_trans h_cj (le_max_right _ _)⟩
          omega
      · -- c.i < m, c.j ≥ m: comparator filtered out
        simp only [hi, hj, dite_true, dite_false]
        apply ih
        · -- Wire times: original depthStep updates wires, restricted doesn't
          intro k
          simp only [Function.update_apply]
          have hk := hwt k
          -- k : Fin m has k.val < m, but c.j.val ≥ m, so ⟨k.val, _⟩ ≠ c.j
          have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
            intro heq; have := congr_arg Fin.val heq; simp at this; omega
          rw [if_neg hkj_n]
          by_cases hki_val : k.val = c.i.val
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
            rw [if_pos hki_n]
            rw [hki_n] at hk
            exact le_trans hk (le_trans (le_max_left _ _) (Nat.le_succ _))
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
            rw [if_neg hki_n]; exact hk
        · exact le_trans hdm (le_max_left _ _)
    · -- c.i ≥ m: both endpoints ≥ m (since c.j > c.i), comparator filtered out
      simp only [hi, dite_false]
      apply ih
      · intro k
        simp only [Function.update_apply]
        have hk := hwt k
        -- k.val < m ≤ c.i.val, so ⟨k.val, _⟩ ≠ c.i
        have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := by
          intro heq; have := congr_arg Fin.val heq; simp at this; omega
        -- c.j > c.i ≥ m > k.val, so ⟨k.val, _⟩ ≠ c.j
        have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
          intro heq; have := congr_arg Fin.val heq; simp at this
          have := c.h; exact absurd (show c.i.val < c.j.val from this) (by omega)
        rw [if_neg hkj_n, if_neg hki_n]; exact hk
      · omega

theorem restrictWires_depth_le {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (hm : m ≤ n) :
    (net.restrictWires m hm).depth ≤ net.depth := by
  simp only [ComparatorNetwork.depth, ComparatorNetwork.restrictWires]
  exact restrictWires_depth_foldl hm net.comparators _ _ _ _
    (fun _ ↦ le_refl _) (le_refl _)


/-! **General execution invariant** -/

/-- General execution invariant for wire restriction: for any `LinearOrder α`,
    if positions `[0, m)` agree between the n-wire and m-wire states, and
    positions `[m, n)` hold values ≥ all values at `[0, m)`, then after
    processing all comparators these invariants are maintained.

    This generalizes the Bool-specific `restrictWires_exec_foldl_bool` below. -/
private lemma restrictWires_exec_foldl_general {n m : ℕ} {α : Type*} [LinearOrder α]
    (hm : m ≤ n)
    (cs : List (Comparator n))
    (w_n : Fin n → α) (w_m : Fin m → α)
    (hinv_lo : ∀ i : Fin m, w_n ⟨i.val, by omega⟩ = w_m i)
    (hinv_hi : ∀ i : Fin n, m ≤ i.val → ∀ j : Fin n, j.val < m → w_n j ≤ w_n i) :
    (∀ i : Fin m,
      cs.foldl (fun acc c ↦ c.apply acc) w_n ⟨i.val, by omega⟩ =
      (cs.filterMap (restrictFilter m)).foldl (fun acc c ↦ c.apply acc) w_m i) ∧
    (∀ i : Fin n, m ≤ i.val → ∀ j : Fin n, j.val < m →
      cs.foldl (fun acc c ↦ c.apply acc) w_n j ≤
      cs.foldl (fun acc c ↦ c.apply acc) w_n i) := by
  induction cs generalizing w_n w_m with
  | nil => exact ⟨hinv_lo, hinv_hi⟩
  | cons c cs ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    unfold restrictFilter
    by_cases hi : c.i.val < m
    · by_cases hj : c.j.val < m
      · -- Both endpoints < m: comparator kept
        simp only [hi, hj, dite_true, List.foldl_cons]
        apply ih
        · -- lo invariant: c.apply w_n agrees with c'.apply w_m at positions < m
          intro k
          simp only [Comparator.apply]
          by_cases hki_val : k.val = c.i.val
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
            have hki_m : k = ⟨c.i.val, hi⟩ := Fin.ext hki_val
            rw [if_pos hki_n, if_pos hki_m]
            congr 1 <;> [exact hinv_lo ⟨c.i.val, hi⟩; exact hinv_lo ⟨c.j.val, hj⟩]
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
            have hki_m : k ≠ ⟨c.i.val, hi⟩ := fun h => hki_val (congr_arg Fin.val h)
            rw [if_neg hki_n, if_neg hki_m]
            by_cases hkj_val : k.val = c.j.val
            · have hkj_n : (⟨k.val, by omega⟩ : Fin n) = c.j := Fin.ext hkj_val
              have hkj_m : k = ⟨c.j.val, hj⟩ := Fin.ext hkj_val
              rw [if_pos hkj_n, if_pos hkj_m]
              congr 1 <;> [exact hinv_lo ⟨c.i.val, hi⟩; exact hinv_lo ⟨c.j.val, hj⟩]
            · have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := fun h => hkj_val (congr_arg Fin.val h)
              have hkj_m : k ≠ ⟨c.j.val, hj⟩ := fun h => hkj_val (congr_arg Fin.val h)
              rw [if_neg hkj_n, if_neg hkj_m]
              exact hinv_lo k
        · -- hi invariant: positions ≥ m still dominate positions < m
          intro i him j hjm
          simp only [Comparator.apply]
          -- i ≥ m but c.i, c.j < m, so i is untouched
          have hne_i : i ≠ c.i := by intro heq; subst heq; omega
          have hne_j_i : i ≠ c.j := by intro heq; subst heq; omega
          rw [if_neg hne_i, if_neg hne_j_i]
          -- j < m and c.i, c.j < m — j could be c.i or c.j
          by_cases hji : j = c.i
          · rw [if_pos hji]
            -- min(w_n(c.i), w_n(c.j)) ≤ w_n(i) since both ≤ w_n(i)
            exact le_trans (min_le_left _ _) (hinv_hi i him c.i (by omega))
          · rw [if_neg hji]
            by_cases hjj : j = c.j
            · rw [if_pos hjj]
              exact max_le (hinv_hi i him c.i (by omega)) (hinv_hi i him c.j (by omega))
            · rw [if_neg hjj]; exact hinv_hi i him j hjm
      · -- c.i < m, c.j ≥ m: cross-boundary comparator, filtered out
        simp only [hi, hj, dite_true, dite_false]
        apply ih
        · -- lo invariant: min(real, pad) = real since pad ≥ real
          intro k
          simp only [Comparator.apply]
          by_cases hki_val : k.val = c.i.val
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
            rw [if_pos hki_n]
            have hpad := hinv_hi c.j (by omega) c.i (by omega)
            rw [min_eq_left hpad, ← hki_n]; exact hinv_lo k
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
            rw [if_neg hki_n]
            have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
              intro heq; have := congr_arg Fin.val heq; simp at this; omega
            rw [if_neg hkj_n]
            exact hinv_lo k
        · -- hi invariant: max(real, pad) = pad, pad stays large
          intro i him j hjm
          simp only [Comparator.apply]
          by_cases hki : i = c.i
          · -- c.i < m but i ≥ m — contradiction
            subst hki; omega
          · rw [if_neg hki]
            by_cases hkj : i = c.j
            · -- i = c.j (pad wire): max(w_n(c.i), w_n(c.j)) ≥ c.apply(w_n)(j)
              rw [if_pos hkj]
              -- j < m, c.i < m: j could be c.i
              by_cases hji : j = c.i
              · rw [if_pos hji]
                -- min(w_n(c.i), w_n(c.j)) ≤ max(w_n(c.i), w_n(c.j))
                exact le_trans (min_le_left _ _) (le_max_left _ _)
              · rw [if_neg hji]
                -- j ≠ c.j since j < m ≤ c.j
                have hjj : j ≠ c.j := by intro heq; subst heq; omega
                rw [if_neg hjj]
                -- w_n(j) ≤ w_n(c.j) ≤ max(w_n(c.i), w_n(c.j))
                exact le_trans (hinv_hi c.j (by omega) j hjm) (le_max_right _ _)
            · rw [if_neg hkj]
              -- i is untouched pad wire, j < m, c.i < m
              by_cases hji : j = c.i
              · rw [if_pos hji]
                -- min(w_n(c.i), w_n(c.j)) ≤ w_n(c.i) ≤ w_n(i)
                exact le_trans (min_le_left _ _) (hinv_hi i him c.i (by omega))
              · rw [if_neg hji]
                have hjj : j ≠ c.j := by intro heq; subst heq; omega
                rw [if_neg hjj]
                exact hinv_hi i him j hjm
    · -- c.i ≥ m: both endpoints ≥ m, comparator filtered, complete no-op for [0,m)
      simp only [hi, dite_false]
      apply ih
      · intro k
        simp only [Comparator.apply]
        have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := by
          intro heq; have := congr_arg Fin.val heq; simp at this; omega
        rw [if_neg hki_n]
        have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
          intro heq; have := congr_arg Fin.val heq; simp at this
          have := c.h; exact absurd (show c.i.val < c.j.val from this) (by omega)
        rw [if_neg hkj_n]; exact hinv_lo k
      · -- Both pad wires: after min/max, values are still ≥ all real values
        intro i him j hjm
        simp only [Comparator.apply]
        -- j < m ≤ c.i < c.j, so j ≠ c.i and j ≠ c.j
        have hne_i_j : j ≠ c.i := by intro heq; subst heq; omega
        have hne_j_j : j ≠ c.j := by
          intro heq; subst heq; have := c.h; omega
        rw [if_neg hne_i_j, if_neg hne_j_j]
        by_cases hki : i = c.i
        · rw [if_pos hki]
          -- min(w_n(c.i), w_n(c.j)) ≥ w_n(j) since both c.i, c.j ≥ m
          exact le_min (hinv_hi c.i (by omega) j hjm) (hinv_hi c.j (by
            have := c.h; omega) j hjm)
        · rw [if_neg hki]
          by_cases hkj : i = c.j
          · rw [if_pos hkj]
            -- max(w_n(c.i), w_n(c.j)) ≥ w_n(j) since c.i ≥ m > j
            exact le_trans (hinv_hi c.i (by omega) j hjm) (le_max_left _ _)
          · rw [if_neg hkj]; exact hinv_hi i him j hjm


/-! **Sorting preservation** -/

/-- Execution invariant for Bool inputs: positions `< m` agree with the
    restricted execution, and positions `≥ m` remain `true`. -/
private lemma restrictWires_exec_foldl {n m : ℕ} (hm : m ≤ n)
    (cs : List (Comparator n))
    (w_n : Fin n → Bool) (w_m : Fin m → Bool)
    (hinv_lo : ∀ i : Fin m, w_n ⟨i.val, by omega⟩ = w_m i)
    (hinv_hi : ∀ i : Fin n, m ≤ i.val → w_n i = true) :
    (∀ i : Fin m,
      cs.foldl (fun acc c ↦ c.apply acc) w_n ⟨i.val, by omega⟩ =
      (cs.filterMap (restrictFilter m)).foldl (fun acc c ↦ c.apply acc) w_m i) ∧
    (∀ i : Fin n, m ≤ i.val →
      cs.foldl (fun acc c ↦ c.apply acc) w_n i = true) := by
  induction cs generalizing w_n w_m with
  | nil => exact ⟨hinv_lo, hinv_hi⟩
  | cons c cs ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    unfold restrictFilter
    by_cases hi : c.i.val < m
    · by_cases hj : c.j.val < m
      · -- Both endpoints < m: comparator kept
        simp only [hi, hj, dite_true, List.foldl_cons]
        apply ih
        · -- lo invariant: c.apply w_n agrees with c'.apply w_m at positions < m
          intro k
          simp only [Comparator.apply]
          by_cases hki_val : k.val = c.i.val
          · -- k maps to c.i
            have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
            have hki_m : k = ⟨c.i.val, hi⟩ := Fin.ext hki_val
            rw [if_pos hki_n, if_pos hki_m]
            congr 1 <;> [exact hinv_lo ⟨c.i.val, hi⟩; exact hinv_lo ⟨c.j.val, hj⟩]
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
            have hki_m : k ≠ ⟨c.i.val, hi⟩ := fun h => hki_val (congr_arg Fin.val h)
            rw [if_neg hki_n, if_neg hki_m]
            by_cases hkj_val : k.val = c.j.val
            · -- k maps to c.j
              have hkj_n : (⟨k.val, by omega⟩ : Fin n) = c.j := Fin.ext hkj_val
              have hkj_m : k = ⟨c.j.val, hj⟩ := Fin.ext hkj_val
              rw [if_pos hkj_n, if_pos hkj_m]
              congr 1 <;> [exact hinv_lo ⟨c.i.val, hi⟩; exact hinv_lo ⟨c.j.val, hj⟩]
            · have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := fun h => hkj_val (congr_arg Fin.val h)
              have hkj_m : k ≠ ⟨c.j.val, hj⟩ := fun h => hkj_val (congr_arg Fin.val h)
              rw [if_neg hkj_n, if_neg hkj_m]
              exact hinv_lo k
        · -- hi invariant: positions ≥ m stay true
          intro i him
          simp only [Comparator.apply]
          have hne_i : i ≠ c.i := by intro heq; subst heq; omega
          have hne_j : i ≠ c.j := by intro heq; subst heq; omega
          rw [if_neg hne_i, if_neg hne_j]
          exact hinv_hi i him
      · -- c.i < m, c.j ≥ m: comparator filtered out
        simp only [hi, hj, dite_true, dite_false]
        apply ih
        · -- lo invariant: c.apply w_n is no-op on positions < m
          intro k
          simp only [Comparator.apply]
          by_cases hki_val : k.val = c.i.val
          · -- k maps to c.i: min(w_n(c.i), w_n(c.j)) where c.j ≥ m so w_n(c.j) = true
            have hki_n : (⟨k.val, by omega⟩ : Fin n) = c.i := Fin.ext hki_val
            rw [if_pos hki_n]
            have hcj_true := hinv_hi c.j (by omega)
            rw [hcj_true, min_eq_left (Bool.le_true _)]
            -- Goal: w_n c.i = w_m k
            -- hinv_lo k : w_n ⟨k.val, _⟩ = w_m k, and ⟨k.val, _⟩ = c.i
            rw [← hki_n]; exact hinv_lo k
          · have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := fun h => hki_val (congr_arg Fin.val h)
            rw [if_neg hki_n]
            -- k.val < m but c.j.val ≥ m, so k ≠ c.j
            have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
              intro heq; have := congr_arg Fin.val heq; simp at this; omega
            rw [if_neg hkj_n]
            exact hinv_lo k
        · -- hi invariant: positions ≥ m stay true
          intro i him
          simp only [Comparator.apply]
          by_cases hki : i = c.i
          · -- c.i < m but i ≥ m — contradiction
            subst hki; omega
          · rw [if_neg hki]
            by_cases hkj : i = c.j
            · -- max(w_n(c.i), w_n(c.j)) where c.j ≥ m so w_n(c.j) = true
              rw [if_pos hkj]
              have := hinv_hi c.j (by omega)
              rw [this, max_eq_right (Bool.le_true _)]
            · rw [if_neg hkj]; exact hinv_hi i him
    · -- c.i ≥ m: both endpoints ≥ m, comparator filtered, complete no-op
      simp only [hi, dite_false]
      apply ih
      · intro k
        simp only [Comparator.apply]
        have hki_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.i := by
          intro heq; have := congr_arg Fin.val heq; simp at this; omega
        rw [if_neg hki_n]
        -- c.j > c.i ≥ m > k.val, so ⟨k.val, _⟩ ≠ c.j
        have hkj_n : (⟨k.val, by omega⟩ : Fin n) ≠ c.j := by
          intro heq; have := congr_arg Fin.val heq; simp at this
          have := c.h; exact absurd (show c.i.val < c.j.val from this) (by omega)
        rw [if_neg hkj_n]; exact hinv_lo k
      · intro i him
        simp only [Comparator.apply]
        have h_ci_true := hinv_hi c.i (by omega)
        have h_cj_true := hinv_hi c.j (by
          have : c.i.val < c.j.val := c.h; omega)
        by_cases hki : i = c.i
        · rw [if_pos hki, h_ci_true, h_cj_true]; simp
        · rw [if_neg hki]
          by_cases hkj : i = c.j
          · rw [if_pos hkj, h_ci_true, h_cj_true]; simp
          · rw [if_neg hkj]; exact hinv_hi i him

/-- Sorting is preserved by wire restriction: if the original network sorts
    all inputs, so does the restricted network. Uses the 0-1 principle to
    reduce to Bool inputs, then shows restricted execution agrees with
    padded execution on positions `[0, m)`. -/
theorem restrictWires_sorts {n : ℕ} (net : ComparatorNetwork n)
    (m : ℕ) (hm : m ≤ n)
    (hsort : ∀ v : Fin n → Bool, Monotone (net.exec v)) :
    (net.restrictWires m hm).Sorts := by
  apply zero_one_principle
  intro v
  -- Pad v with true at positions [m, n)
  let v' : Fin n → Bool := fun i ↦ if h : i.val < m then v ⟨i.val, h⟩ else true
  -- The original network sorts v'
  have hsorted : Monotone (net.exec v') := hsort v'
  -- Restricted execution agrees with padded execution on [0, m)
  have hrestr := (restrictWires_exec_foldl hm net.comparators v' v
    (fun i ↦ by simp [v', i.isLt]) (fun i him ↦ by simp [v', show ¬(i.val < m) by omega])).1
  -- Transfer monotonicity
  intro i j hij
  simp only [ComparatorNetwork.exec, ComparatorNetwork.restrictWires] at hrestr hsorted ⊢
  rw [← hrestr i, ← hrestr j]
  exact hsorted (by exact hij)


/-! **General execution correspondence** -/

/-- `castLE` commutes with a single comparator application:
    running a comparator on `Fin M`-lifted values gives the same
    result as lifting the `Fin n` comparator result. -/
theorem castLE_comparator_apply {n M : ℕ} (hn : n ≤ M) (c : Comparator n)
    (w : Fin n → Fin n) (i : Fin n) :
    c.apply (Fin.castLE hn ∘ w) i = Fin.castLE hn (c.apply w i) := by
  unfold Comparator.apply; simp only [Function.comp]
  split_ifs with h1 h2
  · exact (Monotone.map_min (fun (a b : Fin M) h => h)).symm
  · exact (Monotone.map_max (fun (a b : Fin M) h => h)).symm
  · rfl

/-- Execution correspondence for wire restriction with padding.
    Given `w_n : Fin M → α` (padded values) and `w_m : Fin n → α` (real values)
    that agree on `[0, n)` with pad values dominating real values,
    after executing the M-wire network on `w_n` and the restricted n-wire
    network on `w_m`, the results still agree on `[0, n)`. -/
theorem restrictWires_exec_agree {M n : ℕ} {α : Type*} [LinearOrder α]
    (hn : n ≤ M) (net : ComparatorNetwork M)
    (w_n : Fin M → α) (w_m : Fin n → α)
    (hinv_lo : ∀ i : Fin n, w_n ⟨i.val, by omega⟩ = w_m i)
    (hinv_hi : ∀ i : Fin M, n ≤ i.val → ∀ j : Fin M, j.val < n → w_n j ≤ w_n i)
    (i : Fin n) :
    net.exec w_n ⟨i.val, by omega⟩ = (net.restrictWires n hn).exec w_m i := by
  simp only [ComparatorNetwork.exec, ComparatorNetwork.restrictWires]
  exact (restrictWires_exec_foldl_general hn net.comparators w_n w_m hinv_lo hinv_hi).1 i

end


