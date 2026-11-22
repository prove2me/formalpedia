-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_Correctness
-- name    : GirvingAKS_Bitonic_Correctness
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:33:20.838188+00:00
-- url     : https://prove2.me/theorems/354978e5-2fec-4feb-a95c-c4c9f7d17e8d
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort — Correctness
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/Correctness.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Correctness of Batcher's bitonic sorting network via the 0-1 principle.
--
--   Main results:
--
--   - `bitonicMerge_sorts_bitonic_bool` : bitonic merge sorts bitonic 0-1 inputs
--   - `bitonicSort_sorts_bool`   : bitonic sort produces monotone output on Bool
--   - `bitonicSort_sorts`        : bitonic sort is a sorting network
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/Correctness.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_CompareLayer

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/Correctness.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort — Correctness

  Correctness of Batcher's bitonic sorting network via the 0-1 principle.

  Main results:
  - `bitonicMerge_sorts_bitonic_bool` : bitonic merge sorts bitonic 0-1 inputs
  - `bitonicSort_sorts_bool`   : bitonic sort produces monotone output on Bool
  - `bitonicSort_sorts`        : bitonic sort is a sorting network
-/


section

open Finset

/-! **Bool Threshold Characterization** -/

/-- A monotone Bool function has a threshold: either all false, or there exists `t`
    such that `f i = true ↔ t ≤ i`. -/
theorem mono_bool_threshold {n : Nat} {f : Fin n → Bool} (hf : Monotone f) :
    (∀ i, f i = false) ∨ (∃ t : Nat, t ≤ n ∧ ∀ i : Fin n, f i = true ↔ t ≤ i.val) := by
  by_cases hall : ∀ i : Fin n, f i = false
  · exact Or.inl hall
  · right
    have ⟨j, hj⟩ : ∃ j : Fin n, f j = true := by
      by_contra h; exact hall (fun i ↦ by cases hfi : f i with
        | false => rfl | true => exact absurd ⟨i, hfi⟩ h)
    let S := Finset.univ.filter (fun i : Fin n ↦ f i = true)
    have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    refine ⟨(S.min' hS).val, Nat.le_of_lt (S.min' hS).isLt,
      fun i ↦ ⟨fun hi ↦ ?_, fun hle ↦ ?_⟩⟩
    · exact Fin.le_def.mp (Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    · exact Bool.eq_true_of_true_le ((Finset.mem_filter.mp (Finset.min'_mem S hS)).2 ▸
        hf (Fin.le_def.mpr hle))

/-- An antitone Bool function has a threshold: either all true, or there exists `t`
    such that `g i = true ↔ i < t`. -/
theorem anti_bool_threshold {n : Nat} {g : Fin n → Bool} (hg : Antitone g) :
    (∀ i, g i = true) ∨ (∃ t : Nat, t ≤ n ∧ ∀ i : Fin n, g i = true ↔ i.val < t) := by
  by_cases hall : ∀ i : Fin n, g i = true
  · exact Or.inl hall
  · right
    have : ∃ j : Fin n, g j = false := by
      by_contra h; apply hall; intro i; cases hgi : g i with
        | true => rfl | false => exact absurd ⟨i, hgi⟩ h
    by_cases hsome : ∃ j : Fin n, g j = true
    · let S := Finset.univ.filter (fun i : Fin n ↦ g i = true)
      have hS : S.Nonempty := by
        obtain ⟨j', hj'⟩ := hsome
        exact ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩
      refine ⟨(S.max' hS).val + 1, by omega,
        fun i ↦ ⟨fun hi ↦ ?_, fun hlt ↦ ?_⟩⟩
      · exact Nat.lt_succ_of_le (Fin.le_def.mp
          (Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)))
      · exact Bool.eq_true_of_true_le ((Finset.mem_filter.mp (Finset.max'_mem S hS)).2 ▸
          hg (Fin.le_def.mpr (by omega)))
    · exact ⟨0, Nat.zero_le _, fun i ↦
        ⟨fun hi ↦ absurd ⟨i, hi⟩ hsome, fun h ↦ absurd h (by omega)⟩⟩

/-! **Cross Layer on Two Monotone Halves** -/

/-- After the cross layer on two monotone halves, the left half is bitonic. -/
theorem cross_layer_left_bitonic (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hleft : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩))
    (hright : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩)) :
    IsBitonic01 (fun i : Fin (2^k) ↦ (bitonicCrossLayer k).exec v
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have heq : ∀ i : Fin (2^k),
      (bitonicCrossLayer k).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
      (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
       v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) :=
    bitonicCrossLayer_exec_left k v
  suffices hsuff : IsBitonic01 (fun i : Fin (2^k) ↦
      v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
      v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) by
    convert hsuff using 1; ext i; exact heq i
  -- f is monotone, g is antitone
  -- f i = v(i), g i = v(2^(k+1) - 1 - i) which reverses the right half
  have hf_mono : Monotone (fun i : Fin (2^k) ↦
      v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := hleft
  have hg_anti : Antitone (fun i : Fin (2^k) ↦
      v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) := by
    intro a b hab
    show v ⟨2^(k+1) - 1 - b.val, _⟩ ≤ v ⟨2^(k+1) - 1 - a.val, _⟩
    have : (⟨2^k - 1 - b.val, by omega⟩ : Fin (2^k)) ≤ ⟨2^k - 1 - a.val, by omega⟩ :=
      Fin.mk_le_mk.mpr (by omega)
    have := hright this
    convert this using 2 <;> (ext; simp <;> (try rw [Nat.pow_succ]) <;> omega)
  -- Use threshold characterization to avoid decide wrappers
  rcases mono_bool_threshold hf_mono with hall_f | ⟨tf, htf_le, htf_char⟩
  · -- f all false → AND all false → trivially bitonic
    exact ⟨false, 0, 2^k, Nat.zero_le _, Nat.le.refl, fun i ↦ by
      simp only []
      constructor
      · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
      · intro _; rw [hall_f i]; simp⟩
  · rcases anti_bool_threshold hg_anti with hall_g | ⟨tg, htg_le, htg_char⟩
    · -- g all true → AND = f, true on [tf, n)
      exact ⟨true, tf, 2^k, htf_le, Nat.le.refl, fun i ↦ by
        simp only []
        constructor
        · intro h
          have hfi : v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true := by
            revert h; cases v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ <;> simp
          exact ⟨(htf_char i).mp hfi, i.isLt⟩
        · intro ⟨hlo, _⟩
          have hfi := (htf_char i).mpr hlo
          simp [hfi, hall_g i]⟩
    · by_cases hle : tf ≤ tg
      · -- true values form [tf, tg)
        exact ⟨true, tf, tg, hle, htg_le, fun i ↦ by
          simp only []
          constructor
          · intro h
            have hfi : v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true := by
              revert h; cases v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ <;> simp
            have hgi : v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ = true := by
              revert h
              cases v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ <;>
              cases v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ <;> simp
            exact ⟨(htf_char i).mp hfi, (htg_char i).mp hgi⟩
          · intro ⟨hlo, hhi⟩
            have hfi := (htf_char i).mpr hlo
            have hgi := (htg_char i).mpr hhi
            simp [hfi, hgi]⟩
      · -- tf > tg → no true values, all false
        exact ⟨false, 0, 2^k, Nat.zero_le _, Nat.le.refl, fun i ↦ by
          simp only []
          constructor
          · intro _; exact ⟨Nat.zero_le _, i.isLt⟩
          · intro _
            by_cases hfi : v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true
            · have htfi := (htf_char i).mp hfi
              have hgi_false : ¬(v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ = true) :=
                fun hg ↦ absurd ((htg_char i).mp hg) (by omega)
              cases hg : v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ with
              | false => simp [hfi]
              | true => exact absurd hg hgi_false
            · cases hf : v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ with
              | false => simp
              | true => exact absurd hf hfi⟩

/-- After the cross layer on two monotone halves, the right half is bitonic. -/
theorem cross_layer_right_bitonic (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hleft : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩))
    (hright : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩)) :
    IsBitonic01 (fun i : Fin (2^k) ↦ (bitonicCrossLayer k).exec v
      ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have heq : ∀ i : Fin (2^k),
      (bitonicCrossLayer k).exec v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
      (v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ ||
       v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
    intro i
    have hfin_eq : (⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ : Fin (2^(k+1))) =
        ⟨2^(k+1) - 1 - (2^k - 1 - i.val), by rw [Nat.pow_succ]; omega⟩ := by
      apply Fin.ext; simp only [Nat.pow_succ]; omega
    rw [hfin_eq]
    exact bitonicCrossLayer_exec_right k v ⟨2^k - 1 - i.val, by omega⟩
  suffices hsuff : IsBitonic01 (fun i : Fin (2^k) ↦
      v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ ||
      v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) by
    convert hsuff using 1; ext i; exact heq i
  -- f is antitone (reversed left half), g is monotone (right half)
  have hf_anti : Antitone (fun i : Fin (2^k) ↦
      v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) := by
    intro a b hab
    show v ⟨2^k - 1 - b.val, _⟩ ≤ v ⟨2^k - 1 - a.val, _⟩
    have : (⟨2^k - 1 - b.val, by omega⟩ : Fin (2^k)) ≤ ⟨2^k - 1 - a.val, by omega⟩ :=
      Fin.mk_le_mk.mpr (by omega)
    have := hleft this
    convert this using 2
  have hg_mono : Monotone (fun i : Fin (2^k) ↦
      v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := hright
  -- Use threshold characterization to avoid decide wrappers
  rcases anti_bool_threshold hf_anti with hall_f | ⟨tf, htf_le, htf_char⟩
  · -- f all true → OR all true → trivially bitonic (b=false, empty interval)
    exact ⟨false, 0, 0, Nat.le.refl, Nat.zero_le _, fun i ↦ by
      simp only []
      constructor
      · intro h; rw [hall_f i] at h; simp at h
      · intro ⟨_, h⟩; omega⟩
  · rcases mono_bool_threshold hg_mono with hall_g | ⟨tg, htg_le, htg_char⟩
    · -- g all false → OR = f, true on [0, tf)
      exact ⟨false, tf, 2^k, htf_le, Nat.le.refl, fun i ↦ by
        simp only []
        constructor
        · intro h
          have hgi := hall_g i
          rw [hgi, Bool.or_false] at h
          -- h : v ⟨2^k - 1 - i.val, ...⟩ = false
          -- By threshold: v ⟨2^k - 1 - i.val, ...⟩ = true ↔ i.val < tf
          -- So ¬(i.val < tf), meaning tf ≤ i.val
          have : ¬(i.val < tf) := by
            intro hlt
            have := (htf_char i).mpr hlt
            rw [this] at h; exact Bool.noConfusion h
          exact ⟨by omega, i.isLt⟩
        · intro ⟨hlo, _⟩
          have hgi := hall_g i
          rw [hgi, Bool.or_false]
          -- Need v ⟨2^k - 1 - i.val, ...⟩ = false
          -- By threshold: true ↔ i.val < tf. We have tf ≤ i.val, so false.
          cases hf : v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ with
          | false => rfl
          | true => exact absurd ((htf_char i).mp hf) (by omega)⟩
    · by_cases hle : tf ≤ tg
      · -- false values form [tf, tg) — positions where f=false AND g=false
        exact ⟨false, tf, tg, hle, htg_le, fun i ↦ by
          simp only []
          constructor
          · intro h
            have hfi_neg : ¬(v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hf; rw [hf] at h; simp at h
            have hgi_neg : ¬(v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hg
              cases hf : v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ with
              | true => exact hfi_neg hf
              | false => rw [hf, hg] at h; simp at h
            have htf_le_i : tf ≤ i.val := by
              by_contra hlt; exact hfi_neg ((htf_char i).mpr (by omega))
            have hi_lt_tg : i.val < tg := by
              by_contra hge; exact hgi_neg ((htg_char i).mpr (by omega))
            exact ⟨htf_le_i, hi_lt_tg⟩
          · intro ⟨hlo, hhi⟩
            have hfi_neg : ¬(v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hf; have := (htf_char i).mp hf; omega
            have hgi_neg : ¬(v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hg; have := (htg_char i).mp hg; omega
            cases hf : v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ with
            | true => exact absurd hf hfi_neg
            | false =>
              cases hg : v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ with
              | true => exact absurd hg hgi_neg
              | false => rfl⟩
      · -- tf > tg → all OR values are true (no gap between thresholds)
        exact ⟨false, 0, 0, Nat.le.refl, Nat.zero_le _, fun i ↦ by
          simp only []
          constructor
          · intro h
            have hfi_neg : ¬(v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hf; rw [hf] at h; simp at h
            have hgi_neg : ¬(v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true) := by
              intro hg
              cases hf : v ⟨2^k - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ with
              | true => exact hfi_neg hf
              | false => rw [hf, hg] at h; simp at h
            -- f false: tf ≤ i.val; g false: i.val < tg; but tg < tf → contradiction
            have htf_le_i : tf ≤ i.val := by
              by_contra hlt; exact hfi_neg ((htf_char i).mpr (by omega))
            have hi_lt_tg : i.val < tg := by
              by_contra hge; exact hgi_neg ((htg_char i).mpr (by omega))
            omega
          · intro ⟨_, h⟩; omega⟩

/-- After the cross layer on two monotone halves, left le right. -/
theorem cross_layer_left_le_right (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hleft : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩))
    (hright : Monotone (fun i : Fin (2^k) ↦ v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩)) :
    (∀ i : Fin (2^k), (bitonicCrossLayer k).exec v
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = false) ∨
    (∀ i : Fin (2^k), (bitonicCrossLayer k).exec v
      ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true) := by
  have hcl := bitonicCrossLayer_exec_left k v
  by_cases hall : ∀ i : Fin (2^k), (bitonicCrossLayer k).exec v
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = false
  · exact Or.inl hall
  · right
    have ⟨i₀, hi₀⟩ := Classical.not_forall.mp hall
    have hi₀t : (bitonicCrossLayer k).exec v
        ⟨i₀.val, by have := i₀.isLt; rw [Nat.pow_succ]; omega⟩ = true := by
      cases h : (bitonicCrossLayer k).exec v ⟨i₀.val, _⟩ with
      | false => exact absurd h hi₀
      | true => rfl
    rw [hcl i₀, Bool.and_eq_true] at hi₀t
    intro j
    have hj2 : (bitonicCrossLayer k).exec v ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩ =
        (v ⟨2^k - 1 - j.val, by rw [Nat.pow_succ]; omega⟩ ||
         v ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) := by
      have hfin_eq : (⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩ : Fin (2^(k+1))) =
          ⟨2^(k+1) - 1 - (2^k - 1 - j.val), by rw [Nat.pow_succ]; omega⟩ := by
        apply Fin.ext; simp only [Nat.pow_succ]; omega
      rw [hfin_eq]
      exact bitonicCrossLayer_exec_right k v ⟨2^k - 1 - j.val, by omega⟩
    rw [hj2, Bool.or_eq_true]
    by_cases hj : j.val ≤ 2^k - 1 - i₀.val
    · left
      -- Need: v ⟨2^k - 1 - j.val, ...⟩ = true
      -- From: v ⟨i₀.val, ...⟩ = true and hleft monotone and i₀.val ≤ 2^k - 1 - j.val
      have hle_fin : (i₀ : Fin (2^k)) ≤ ⟨2^k - 1 - j.val, by have := j.isLt; omega⟩ := by
        simp only [Fin.le_def]; have := i₀.isLt; have := j.isLt; omega
      have := hleft hle_fin
      exact Bool.eq_true_of_true_le (hi₀t.1 ▸ this)
    · right
      have hright_at : v ⟨2^(k+1) - 1 - i₀.val, by rw [Nat.pow_succ]; omega⟩ =
          v ⟨(2^k - 1 - i₀.val) + 2^k, by rw [Nat.pow_succ]; omega⟩ := by
        congr 1; apply Fin.ext; simp only [Nat.pow_succ]; omega
      have hle_fin : (⟨2^k - 1 - i₀.val, by omega⟩ : Fin (2^k)) ≤ ⟨j.val, j.isLt⟩ := by
        simp only [Fin.le_def]; have := i₀.isLt; have := j.isLt; omega
      have := hright hle_fin
      exact Bool.eq_true_of_true_le ((hright_at ▸ hi₀t.2) ▸ this)

/-! **Bitonic Sort** -/

/-- Bitonic sort produces monotone output on Bool inputs. -/
theorem bitonicSort_sorts_bool :
    ∀ (k : Nat) (v : Fin (2^k) → Bool), Monotone ((bitonicSort k).exec v) := by
  intro k
  induction k with
  | zero =>
    intro v a b _
    have ha : a = ⟨0, by omega⟩ := Fin.ext (by omega)
    have hb : b = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [ha, hb]
  | succ k ih =>
    intro v
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    -- Decompose the execution
    have hdecomp := bitonicSort_exec_eq k v
    -- After sorting both halves
    set v1 := ((bitonicSort k).shiftEmbed (2^(k+1)) 0 h0).exec v
    set v2 := ((bitonicSort k).shiftEmbed (2^(k+1)) (2^k) h1).exec v1
    -- Left half of v2 is monotone (sorted by bitonicSort k)
    have hv2_left : Monotone (fun i : Fin (2^k) ↦ v2 ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
      have hv2_i : ∀ i : Fin (2^k), v2 ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
          v1 ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ :=
        fun i ↦ ComparatorNetwork.shiftEmbed_exec_outside _ _ _ _ _ _ (Or.inl (by show i.val < 2^k; exact i.isLt))
      have hv1_i : ∀ i : Fin (2^k), v1 ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
          (bitonicSort k).exec (fun j ↦ v ⟨j.val, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) i :=
        fun i ↦ shiftEmbed_zero_exec _ _ _ _ i
      intro a b hab
      show v2 ⟨a.val, _⟩ ≤ v2 ⟨b.val, _⟩
      rw [hv2_i a, hv2_i b, hv1_i a, hv1_i b]
      exact ih _ hab
    have hv2_right : Monotone (fun i : Fin (2^k) ↦ v2 ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
      have hv2_i : ∀ i : Fin (2^k), v2 ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
          (bitonicSort k).exec (fun j ↦ v1 ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) i :=
        fun i ↦ shiftEmbed_offset_exec _ _ _ _ _ i
      have hv1_j : ∀ j : Fin (2^k), v1 ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩ =
          v ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩ :=
        fun j ↦ ComparatorNetwork.shiftEmbed_exec_outside _ _ _ _ _ _ (Or.inr (by show 0 + 2^k ≤ j.val + 2^k; omega))
      intro a b hab
      show v2 ⟨a.val + 2^k, _⟩ ≤ v2 ⟨b.val + 2^k, _⟩
      rw [hv2_i a, hv2_i b]
      have heq : (fun j : Fin (2^k) ↦ v1 ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) =
          (fun j ↦ v ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩) :=
        funext hv1_j
      rw [heq]
      exact ih _ hab
    -- After cross layer
    set v3 := (bitonicCrossLayer k).exec v2
    have hv3_left_bito := cross_layer_left_bitonic k v2 hv2_left hv2_right
    have hv3_right_bito := cross_layer_right_bitonic k v2 hv2_left hv2_right
    have hv3_lr := cross_layer_left_le_right k v2 hv2_left hv2_right
    -- Local views after cross
    set wL : Fin (2^k) → Bool := fun i ↦ v3 ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set wR : Fin (2^k) → Bool := fun i ↦ v3 ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    have hml : Monotone ((bitonicMerge k).exec wL) := bitonicMerge_sorts_bitonic_bool k wL hv3_left_bito
    have hmr : Monotone ((bitonicMerge k).exec wR) := bitonicMerge_sorts_bitonic_bool k wR hv3_right_bito
    -- Characterize the full output at each position
    have hout_left : ∀ i : Fin (2^k),
        (bitonicSort (k + 1)).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
        (bitonicMerge k).exec wL i := by
      intro i; rw [hdecomp]; exact merge_result_left k v3 h0 h1 wL rfl i
    have hout_right : ∀ i : Fin (2^k),
        (bitonicSort (k + 1)).exec v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
        (bitonicMerge k).exec wR i := by
      intro i; rw [hdecomp]; exact merge_result_right k v3 h0 h1 wR rfl i
    -- Prove monotonicity
    intro a b hab
    by_cases ha : a.val < 2^k
    · by_cases hb : b.val < 2^k
      · have ha' : (a : Fin (2^(k+1))) = ⟨a.val, a.isLt⟩ := rfl
        have hb' : (b : Fin (2^(k+1))) = ⟨b.val, b.isLt⟩ := rfl
        rw [ha', hb', hout_left ⟨a.val, ha⟩, hout_left ⟨b.val, hb⟩]
        exact hml (Fin.mk_le_mk.mpr hab)
      · have ha' : (a : Fin (2^(k+1))) = ⟨a.val, a.isLt⟩ := rfl
        have hb_eq : (b : Fin (2^(k+1))) = ⟨(b.val - 2^k) + 2^k, by omega⟩ :=
          Fin.ext (by show b.val = (b.val - 2^k) + 2^k; omega)
        rw [ha', hout_left ⟨a.val, ha⟩, hb_eq, hout_right ⟨b.val - 2^k, by omega⟩]
        rcases hv3_lr with hlr | hlr
        · have : wL = fun _ ↦ false := funext hlr
          rw [this, exec_allFalse_eq]; exact Bool.false_le _
        · have : wR = fun _ ↦ true := funext hlr
          rw [this, exec_allTrue_eq]; exact Bool.le_true _
    · have ha_eq : (bitonicSort (k+1)).exec v a =
          (bitonicMerge k).exec wR ⟨a.val - 2^k, by omega⟩ := by
        conv_lhs => rw [show (a : Fin (2^(k+1))) = ⟨(a.val - 2^k) + 2^k, by omega⟩ from
          Fin.ext (by show a.val = (a.val - 2^k) + 2^k; omega)]
        exact hout_right ⟨a.val - 2^k, by omega⟩
      have hb_eq : (bitonicSort (k+1)).exec v b =
          (bitonicMerge k).exec wR ⟨b.val - 2^k, by omega⟩ := by
        conv_lhs => rw [show (b : Fin (2^(k+1))) = ⟨(b.val - 2^k) + 2^k, by omega⟩ from
          Fin.ext (by show b.val = (b.val - 2^k) + 2^k; omega)]
        exact hout_right ⟨b.val - 2^k, by omega⟩
      rw [ha_eq, hb_eq]
      exact hmr (Fin.mk_le_mk.mpr (by omega))

/-- Bitonic sort is a sorting network. -/
theorem bitonicSort_sorts (k : Nat) : (bitonicSort k).Sorts :=
  zero_one_principle _ (bitonicSort_sorts_bool k)

end


