-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_Bitonic01
-- name    : GirvingAKS_Bitonic_Bitonic01
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:54.149046+00:00
-- url     : https://prove2.me/theorems/3030173c-f33c-4100-96e5-85cd4b1119f6
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic 0-1 Sequences
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/Bitonic01.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** `IsBitonic01` definition, basic facts, interval helpers for and/or of bitonic inputs.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/Bitonic01.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/Bitonic01.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic 0-1 Sequences

  `IsBitonic01` definition, basic facts, interval helpers for and/or of bitonic inputs.
-/


section

open Finset

/-! **Bitonic 0-1 Sequences** -/

/-- A 0-1 sequence is *bitonic* if some Bool value forms a contiguous interval `[lo, hi)`.
    Equivalently, the sequence has at most two "transitions" between false and true
    (a rotation of a monotone sequence). -/
def IsBitonic01 {n : Nat} (v : Fin n → Bool) : Prop :=
  ∃ (b : Bool) (lo hi : Nat), lo ≤ hi ∧ hi ≤ n ∧
    (∀ i : Fin n, v i = b ↔ lo ≤ i.val ∧ i.val < hi)

/-- A monotone 0-1 sequence is bitonic (the false block is `[0, t₀)` where `t₀` is
    the first true position). -/
theorem monotone_isBitonic01 {n : Nat} {v : Fin n → Bool} (hv : Monotone v) :
    IsBitonic01 v := by
  by_cases h_all : ∀ i : Fin n, v i = false
  · exact ⟨false, 0, n, Nat.zero_le _, Nat.le.refl,
      fun i ↦ ⟨fun _ ↦ ⟨Nat.zero_le _, i.isLt⟩, fun _ ↦ h_all i⟩⟩
  · have ⟨t, ht⟩ : ∃ t : Fin n, v t ≠ false := by
      by_contra hall; exact h_all (fun i ↦ by by_contra hi; exact hall ⟨i, hi⟩)
    have ht_true : v t = true := by cases hv : v t <;> simp_all
    have h_up : ∀ i j : Fin n, i ≤ j → v i = true → v j = true :=
      fun i j hij hi ↦ Bool.eq_true_of_true_le (hi ▸ hv hij)
    let S := Finset.univ.filter (fun i : Fin n ↦ v i = true)
    have hS : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht_true⟩⟩
    let t₀ := S.min' hS
    have ht₀_true : v t₀ = true := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    have ht₀_min : ∀ i : Fin n, v i = true → t₀ ≤ i :=
      fun i hi ↦ Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    exact ⟨false, 0, t₀.val, Nat.zero_le _, Nat.le_of_lt t₀.isLt,
      fun i ↦ ⟨fun hf ↦ ⟨Nat.zero_le _, by
        by_contra hge
        have hle : t₀ ≤ i := Fin.le_def.mpr (by omega)
        exact absurd (h_up t₀ i hle ht₀_true) (by rw [hf]; decide)⟩,
        fun ⟨_, hi⟩ ↦ by
          by_contra hne
          have htrue : v i = true := by cases hv : v i <;> simp_all
          have hle := ht₀_min i htrue
          exact absurd hle (not_le.mpr (Fin.lt_def.mpr hi))⟩⟩

/-- All-false is bitonic. -/
theorem allFalse_isBitonic01 {n : Nat} : IsBitonic01 (fun _ : Fin n ↦ false) :=
  ⟨false, 0, n, Nat.zero_le _, Nat.le.refl,
    fun i ↦ ⟨fun _ ↦ ⟨Nat.zero_le _, i.isLt⟩, fun _ ↦ rfl⟩⟩

/-- All-true is bitonic. -/
theorem allTrue_isBitonic01 {n : Nat} : IsBitonic01 (fun _ : Fin n ↦ true) :=
  ⟨false, 0, 0, Nat.le.refl, Nat.zero_le n,
    fun _ ↦ ⟨fun h ↦ Bool.noConfusion h, fun ⟨_, h⟩ ↦ absurd h (by omega)⟩⟩

/-! **Interval Helpers for Compare Layer** -/

/-- Helper to get clean `Fin.val` characterization from the `IsBitonic01` hypothesis. -/
theorem isBitonic01_val_left {m : Nat} {v : Fin (2 * m) → Bool} {b : Bool} {lo hi : Nat}
    (hv : ∀ j : Fin (2 * m), v j = b ↔ lo ≤ j.val ∧ j.val < hi) (i : Fin m) :
    v ⟨i.val, by omega⟩ = b ↔ lo ≤ i.val ∧ i.val < hi := by
  have := hv ⟨i.val, by omega⟩; simpa using this

theorem isBitonic01_val_right {m : Nat} {v : Fin (2 * m) → Bool} {b : Bool} {lo hi : Nat}
    (hv : ∀ j : Fin (2 * m), v j = b ↔ lo ≤ j.val ∧ j.val < hi) (i : Fin m) :
    v ⟨i.val + m, by omega⟩ = b ↔ lo ≤ i.val + m ∧ i.val + m < hi := by
  have := hv ⟨i.val + m, by omega⟩; simpa using this

/-- AND of bitonic input (b=false case). -/
theorem and_bitonic_false {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = false ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨false, lo, hi, _hlo, h1, fun i ↦ ?_⟩
    rw [Bool.and_eq_false_iff]; constructor
    · intro h; rcases h with h | h
      · exact (hvi i).mp h
      · exact absurd ((hvim i).mp h) (by omega)
    · intro h; exact Or.inl ((hvi i).mpr h)
  · by_cases h2 : m ≤ lo
    · refine ⟨false, lo - m, hi - m, by omega, by omega, fun i ↦ ?_⟩
      rw [Bool.and_eq_false_iff]; constructor
      · intro h; rcases h with h | h
        · exact absurd ((hvi i).mp h) (by omega)
        · have := (hvim i).mp h; omega
      · intro h; exact Or.inr ((hvim i).mpr (by omega))
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨false, 0, m, Nat.zero_le _, Nat.le.refl, fun i ↦ ?_⟩
        rw [Bool.and_eq_false_iff]; constructor
        · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
        · intro _
          by_cases h : lo ≤ i.val
          · exact Or.inl ((hvi i).mpr ⟨h, by omega⟩)
          · exact Or.inr ((hvim i).mpr (by omega))
      · refine ⟨true, hi - m, lo, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩
          have hni : ¬(lo ≤ i.val ∧ i.val < hi) := fun hc ↦ by
            have := (hvi i).mpr hc; rw [h1] at this; exact Bool.noConfusion this
          have hnim : ¬(lo ≤ i.val + m ∧ i.val + m < hi) := fun hc ↦ by
            have := (hvim i).mpr hc; rw [h2] at this; exact Bool.noConfusion this
          omega
        · intro ⟨h1, h2⟩
          exact ⟨by cases hv' : v ⟨i.val, by omega⟩ with
                   | false => exact absurd ((hvi i).mp hv') (by omega)
                   | true => rfl,
                 by cases hv' : v ⟨i.val + m, by omega⟩ with
                   | false => exact absurd ((hvim i).mp hv') (by omega)
                   | true => rfl⟩

/-- AND of bitonic input (b=true case). -/
theorem and_bitonic_true {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = true ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
    rw [Bool.and_eq_true]; constructor
    · intro ⟨_, h2⟩; have := (hvim i).mp h2; omega
    · intro ⟨_, h⟩; omega
  · by_cases h2 : m ≤ lo
    · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
      rw [Bool.and_eq_true]; constructor
      · intro ⟨h1, _⟩; have := (hvi i).mp h1; omega
      · intro ⟨_, h⟩; omega
    · by_cases h3 : hi - m ≤ lo
      · refine ⟨true, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩; have := (hvi i).mp h1; have := (hvim i).mp h2; omega
        · intro ⟨_, h⟩; omega
      · refine ⟨true, lo, hi - m, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.and_eq_true]; constructor
        · intro ⟨h1, h2⟩; exact ⟨((hvi i).mp h1).1, by have := (hvim i).mp h2; omega⟩
        · intro ⟨h1, h2⟩; exact ⟨(hvi i).mpr ⟨h1, by omega⟩, (hvim i).mpr (by omega)⟩

/-- OR of bitonic input (b=false case). -/
theorem or_bitonic_false {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = false ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
    rw [Bool.or_eq_false_iff]; constructor
    · intro ⟨_, h2⟩; exact absurd ((hvim i).mp h2) (by omega)
    · intro ⟨_, h⟩; omega
  · by_cases h2 : m ≤ lo
    · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
      rw [Bool.or_eq_false_iff]; constructor
      · intro ⟨h1, _⟩; exact absurd ((hvi i).mp h1) (by omega)
      · intro ⟨_, h⟩; omega
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨false, lo, hi - m, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩; exact ⟨((hvi i).mp h1).1, by have := (hvim i).mp h2; omega⟩
        · intro ⟨h1, h2⟩; exact ⟨(hvi i).mpr ⟨h1, by omega⟩, (hvim i).mpr (by omega)⟩
      · refine ⟨false, 0, 0, Nat.le.refl, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩; have := (hvi i).mp h1; have := (hvim i).mp h2; omega
        · intro ⟨_, h⟩; omega

/-- OR of bitonic input (b=true case). -/
theorem or_bitonic_true {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = true ↔ lo ≤ j.val ∧ j.val < hi) :
    ∃ (b : Bool) (lo' hi' : Nat), lo' ≤ hi' ∧ hi' ≤ m ∧
      ∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = b ↔
        lo' ≤ i.val ∧ i.val < hi' := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases h1 : hi ≤ m
  · refine ⟨true, lo, hi, _hlo, h1, fun i ↦ ?_⟩
    rw [Bool.or_eq_true]; constructor
    · intro h; rcases h with h | h
      · exact (hvi i).mp h
      · exact absurd ((hvim i).mp h) (by omega)
    · intro h; exact Or.inl ((hvi i).mpr h)
  · by_cases h2 : m ≤ lo
    · refine ⟨true, lo - m, hi - m, by omega, by omega, fun i ↦ ?_⟩
      rw [Bool.or_eq_true]; constructor
      · intro h; rcases h with h | h
        · exact absurd ((hvi i).mp h) (by omega)
        · have := (hvim i).mp h; omega
      · intro h; exact Or.inr ((hvim i).mpr (by omega))
    · by_cases h3 : lo ≤ hi - m
      · refine ⟨true, 0, m, Nat.zero_le _, Nat.le.refl, fun i ↦ ?_⟩
        rw [Bool.or_eq_true]; constructor
        · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
        · intro _
          by_cases h : lo ≤ i.val
          · exact Or.inl ((hvi i).mpr ⟨h, by omega⟩)
          · exact Or.inr ((hvim i).mpr (by omega))
      · refine ⟨false, hi - m, lo, by omega, by omega, fun i ↦ ?_⟩
        rw [Bool.or_eq_false_iff]; constructor
        · intro ⟨h1, h2⟩
          have hni : ¬(lo ≤ i.val ∧ i.val < hi) := fun hc ↦ by
            have := (hvi i).mpr hc; rw [h1] at this; exact Bool.noConfusion this
          have hnim : ¬(lo ≤ i.val + m ∧ i.val + m < hi) := fun hc ↦ by
            have := (hvim i).mpr hc; rw [h2] at this; exact Bool.noConfusion this
          omega
        · intro ⟨h1, h2⟩
          exact ⟨by cases hv' : v ⟨i.val, by omega⟩ with
                   | true => exact absurd ((hvi i).mp hv') (by omega)
                   | false => rfl,
                 by cases hv' : v ⟨i.val + m, by omega⟩ with
                   | true => exact absurd ((hvim i).mp hv') (by omega)
                   | false => rfl⟩

end


