-- Prove2me | Definitions.Def_GirvingAKS_Bags_SepBridge
-- name    : GirvingAKS_Bags_SepBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:07:00.030268+00:00
-- url     : https://prove2.me/theorems/9e78ee8b-590d-4592-bb9a-bb857ad110eb
-- title:
--   AKS sorting networks (Seiferas port) — Separator-Stranger Bridge Infrastructure
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/SepBridge.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Connects the separator property (`IsSeparator`/`SepInitial`/`SepFinal`) to stranger counting for the proof of `separator_middle_stranger_le`.
--
--   Key insight: strangers have values outside the ancestor interval [lo, hi):
--
--   - Low strangers: value < lo (the L smallest values in the bag)
--   - High strangers: value ≥ hi (the H largest values in the bag)
--
--   After the separator approximately sorts:
--
--   - Small values go to small positions (low fringe)
--   - Large values go to large positions (high fringe)
--   - The middle [f, s-f) gets ≤ ε·L low strangers + ε·H high strangers = ε·T
--
--   The separator property uses local ranks, not global values. The decomposition `u = g ∘ σ` (where g is strictly monotone and σ is a permutation) lets us translate between the two via `exec_comp_mono`.
--
--   Contains:
--
--   - `separator_injective_initial` / `separator_injective_final`: injective-input separator bounds
--   - `stage_exec_on_regs`: stage execution on bag registers acts like that bag's separator
--   - `separator_filter_strangers`: separator filters strangers by factor ε
--   - `parent_stranger_j2_le`: j ≥ 2 stranger bound via separator filtering + IH
--   - Assembly algebra and complement counting helpers
--   - `odd_geom_sum_le`: partial geometric sum bound
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/SepBridge.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Filter

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/SepBridge.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Separator-Stranger Bridge Infrastructure

  Connects the separator property (`IsSeparator`/`SepInitial`/`SepFinal`) to stranger
  counting for the proof of `separator_middle_stranger_le`.

  Key insight: strangers have values outside the ancestor interval [lo, hi):
  - Low strangers: value < lo (the L smallest values in the bag)
  - High strangers: value ≥ hi (the H largest values in the bag)

  After the separator approximately sorts:
  - Small values go to small positions (low fringe)
  - Large values go to large positions (high fringe)
  - The middle [f, s-f) gets ≤ ε·L low strangers + ε·H high strangers = ε·T

  The separator property uses local ranks, not global values. The decomposition
  `u = g ∘ σ` (where g is strictly monotone and σ is a permutation) lets us
  translate between the two via `exec_comp_mono`.

  Contains:
  - `separator_injective_initial` / `separator_injective_final`: injective-input separator bounds
  - `stage_exec_on_regs`: stage execution on bag registers acts like that bag's separator
  - `separator_filter_strangers`: separator filters strangers by factor ε
  - `parent_stranger_j2_le`: j ≥ 2 stranger bound via separator filtering + IH
  - Assembly algebra and complement counting helpers
  - `odd_geom_sum_le`: partial geometric sum bound
-/


section

open Finset

variable {k : ℕ}

/-! **Separator-Stranger Bridge Infrastructure**

The proof of `separator_middle_stranger_le` requires connecting the separator
property (`IsSeparator`/`SepInitial`/`SepFinal`) to stranger counting.

Key insight: strangers have values outside the ancestor interval [lo, hi):
- Low strangers: value < lo (the L smallest values in the bag)
- High strangers: value ≥ hi (the H largest values in the bag)

After the separator approximately sorts:
- Small values go to small positions (low fringe)
- Large values go to large positions (high fringe)
- The middle [f, s-f) gets ≤ ε·L low strangers + ε·H high strangers = ε·T

The separator property uses local ranks, not global values. The decomposition
`u = g ∘ σ` (where g is strictly monotone and σ is a permutation) lets us
translate between the two via `exec_comp_mono`. -/

/-- Decompose an injective `u : Fin C → Fin n` into `g ∘ σ` where `g` is strictly monotone
    and `σ` is a permutation, with network execution compatibility and count transfer.
    Used by both `separator_injective_initial` and `separator_injective_final`. -/
theorem injective_monotone_perm_decomp {C n : ℕ}
    (net : ComparatorNetwork C)
    (u : Fin C → Fin n) (hu : Function.Injective u) :
    ∃ (g : Fin C → Fin n) (σ : Equiv.Perm (Fin C)),
      StrictMono g ∧
      (∀ j, u j = g (σ j)) ∧
      net.exec u = g ∘ net.exec (⇑σ) ∧
      (∀ (P : Fin n → Prop) [DecidablePred P],
        (univ.filter (fun i : Fin C ↦ P (u i))).card =
        (univ.filter (fun r : Fin C ↦ P (g r))).card) := by
  set S := univ.image u
  have hcard : S.card = C := by
    rw [card_image_of_injective _ hu, card_univ, Fintype.card_fin]
  set g_iso := S.orderIsoOfFin hcard
  set g : Fin C → Fin n := fun i ↦ (g_iso i).val
  have hg_strict : StrictMono g := fun a b hab ↦ g_iso.strictMono hab
  have hmem : ∀ j, u j ∈ S := fun j ↦ mem_image.mpr ⟨j, mem_univ _, rfl⟩
  set σ_fun : Fin C → Fin C := fun j ↦ g_iso.symm ⟨u j, hmem j⟩
  have hσ_inj : Function.Injective σ_fun := by
    intro j₁ j₂ heq
    have h' : (⟨u j₁, hmem j₁⟩ : ↥S) = ⟨u j₂, hmem j₂⟩ := g_iso.symm.injective heq
    exact hu (Subtype.ext_iff.mp h')
  set σ : Equiv.Perm (Fin C) := Equiv.ofBijective σ_fun
    ((Finite.injective_iff_bijective).mp hσ_inj)
  have hu_eq : ∀ j, u j = g (σ j) := by
    intro j; show u j = (g_iso (g_iso.symm ⟨u j, hmem j⟩)).val
    simp [g_iso.apply_symm_apply]
  have hexec : net.exec u = g ∘ net.exec (⇑σ) := by
    have heq : u = g ∘ ⇑σ := funext hu_eq
    rw [heq]; exact ComparatorNetwork.exec_comp_mono net (StrictMono.monotone hg_strict) (⇑σ)
  refine ⟨g, σ, hg_strict, hu_eq, hexec, fun P _ ↦ ?_⟩
  apply card_nbij' σ σ.symm
  · intro i hi
    simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
    rw [← hu_eq i]; exact hi
  · intro r hr
    simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hr ⊢
    rw [hu_eq (σ.symm r), σ.apply_symm_apply]; exact hr
  · intro _ _; simp
  · intro _ _; simp

/-- Apply `SepInitial` to injective (not just permutation) inputs.
    Analogous to `halver_injective_initial_halved` but for general separators.

    Given an injective input `u : Fin (2*m) → Fin n`, decomposes `u = g ∘ σ`
    where `g` is strictly monotone (the sorted enumeration) and `σ` is a
    permutation. Then uses `exec_comp_mono` to reduce to `σ` and applies
    `SepInitial` from the separator property.

    The count `a = |{i : u(i) < threshold}|` corresponds to the number of
    items with "small" values. The bound says that ≤ ε·a of these end up
    at positions ≥ ⌊γ·(2m)⌋₊ (i.e., outside the low fringe). -/
theorem separator_injective_initial {m n : ℕ}
    {net : ComparatorNetwork (2 * m)} {γ ε : ℝ}
    (hnet : IsSeparator net γ ε) (hγ : 0 ≤ γ)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold : ℕ) :
    let C := 2 * m
    let a := (univ.filter (fun i : Fin C ↦ (u i).val < threshold)).card
    let boundary := ⌊γ * ↑C⌋₊
    a ≤ boundary →
    ((univ.filter (fun pos : Fin C ↦
        boundary ≤ pos.val ∧ (net.exec u pos).val < threshold)).card : ℝ) ≤ ε * ↑a := by
  intro C a boundary ha
  -- Trivial case: a = 0
  by_cases ha0 : a = 0
  · simp only [ha0, Nat.cast_zero, mul_zero]
    suffices h : (univ.filter (fun pos : Fin C ↦
        boundary ≤ pos.val ∧ (net.exec u pos).val < threshold)).card = 0 by
      simp [h]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro pos
    simp only [mem_filter, mem_univ, true_and, not_and, not_lt]
    intro _
    have hu_ge : ∀ i, threshold ≤ (u i).val := by
      intro i; by_contra h_lt; push_neg at h_lt
      have : i ∈ univ.filter (fun i : Fin C ↦ (u i).val < threshold) :=
        mem_filter.mpr ⟨mem_univ _, h_lt⟩
      exact absurd (Finset.card_pos.mpr ⟨i, this⟩) (by omega)
    have hmem : net.exec u pos ∈ Set.range u := by
      rw [← net.exec_range_eq u]; exact Set.mem_range_self pos
    obtain ⟨i, hi⟩ := hmem
    calc threshold ≤ (u i).val := hu_ge i
      _ = (net.exec u pos).val := by rw [hi]
  -- Decompose u = g ∘ σ
  obtain ⟨g, σ, hg_strict, hu_eq, hexec, hcount⟩ := injective_monotone_perm_decomp net u hu
  have ha_eq : a = (univ.filter (fun r : Fin C ↦ (g r).val < threshold)).card :=
    hcount (fun v ↦ v.val < threshold)
  -- Threshold translation: (g r).val < threshold ↔ r.val < a
  have hthresh : ∀ r : Fin C, (g r).val < threshold ↔ r.val < a := by
    rw [ha_eq]; exact strictMono_threshold hg_strict threshold
  -- Rewrite filter using threshold translation
  have hfilter_eq : univ.filter (fun pos : Fin C ↦
      boundary ≤ pos.val ∧ (net.exec u pos).val < threshold) =
    univ.filter (fun pos : Fin C ↦
      boundary ≤ pos.val ∧ (net.exec (⇑σ) pos).val < a) := by
    ext pos; simp only [mem_filter, mem_univ, true_and]
    exact and_congr_right fun _ ↦ by
      have := congr_fun hexec pos; simp only [Function.comp] at this; rw [this]; exact hthresh _
  rw [hfilter_eq]
  -- Apply SepInitial with γ' = a / C
  have hsep := (hnet σ).1
  have hγ'_le : (a : ℝ) / ↑C ≤ γ := by
    have h1 : (a : ℝ) ≤ boundary := by exact_mod_cast ha
    have h2 : (boundary : ℝ) ≤ γ * ↑C := Nat.floor_le (mul_nonneg hγ (Nat.cast_nonneg _))
    by_cases hC0 : C = 0
    · simp [hC0, hγ]
    · have hC_pos : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC0
      have hab : (a : ℝ) ≤ γ * ↑C := h1.trans h2
      calc (a : ℝ) / ↑C ≤ (γ * ↑C) / ↑C :=
          div_le_div_of_nonneg_right hab (le_of_lt hC_pos)
        _ = γ := by field_simp
  have hγ'_nn : 0 ≤ (a : ℝ) / ↑C := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsep_app := hsep ((a : ℝ) / ↑C) hγ'_nn hγ'_le
  simp only [Fintype.card_fin, rank_fin_val] at hsep_app
  by_cases hC0 : C = 0
  · -- C = 0 means m = 0, Fin 0 is empty, a = 0, contradicting ha0
    have hm0 : m = 0 := by omega
    subst hm0; exact absurd rfl ha0
  have hC_pos : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC0
  have hfloor_a : ⌊(a : ℝ) / ↑C * ↑C⌋₊ = a := by
    rw [div_mul_cancel₀ _ (ne_of_gt hC_pos)]
    exact Nat.floor_natCast a
  rw [hfloor_a] at hsep_app
  have hbound : ε * ((a : ℝ) / ↑C) * ↑C = ε * ↑a := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hC_pos)]
  rw [hbound] at hsep_app
  have hsep_app' : (↑(univ.filter (fun pos : Fin C ↦
      ⌊γ * ↑C⌋₊ ≤ rank pos ∧ rank (net.exec (⇑σ) pos) < a)).card : ℝ) ≤ ε * ↑a := by
    simp only [rank_fin_val] at hsep_app ⊢
    exact hsep_app
  calc ((univ.filter (fun pos : Fin C ↦
        boundary ≤ pos.val ∧ (net.exec (⇑σ) pos).val < a)).card : ℝ)
      ≤ ((univ.filter (fun pos : Fin C ↦
          ⌊γ * ↑C⌋₊ ≤ rank pos ∧ rank (net.exec (⇑σ) pos) < a)).card : ℝ) := by
        apply Nat.cast_le.mpr; apply card_le_card
        intro pos hp
        simp only [mem_filter, mem_univ, true_and, rank_fin_val] at hp ⊢
        exact hp
    _ ≤ ε * ↑a := hsep_app'

/-- Apply `SepFinal` to injective inputs (dual of `separator_injective_initial`).
    For items with value ≥ threshold (the H largest), bounds how many end up
    at positions < C - ⌊γ·C⌋₊ (i.e., outside the high fringe). -/
theorem separator_injective_final {m n : ℕ}
    {net : ComparatorNetwork (2 * m)} {γ ε : ℝ}
    (hnet : IsSeparator net γ ε) (hγ : 0 ≤ γ)
    (u : Fin (2 * m) → Fin n) (hu : Function.Injective u) (threshold : ℕ) :
    let C := 2 * m
    let a := (univ.filter (fun i : Fin C ↦ threshold ≤ (u i).val)).card
    let boundary := C - ⌊γ * ↑C⌋₊
    a ≤ ⌊γ * ↑C⌋₊ →
    ((univ.filter (fun pos : Fin C ↦
        pos.val < boundary ∧ threshold ≤ (net.exec u pos).val)).card : ℝ) ≤ ε * ↑a := by
  intro C a boundary ha
  -- Trivial case: a = 0
  by_cases ha0 : a = 0
  · simp only [ha0, Nat.cast_zero, mul_zero]
    suffices h : (univ.filter (fun pos : Fin C ↦
        pos.val < boundary ∧ threshold ≤ (net.exec u pos).val)).card = 0 by
      simp [h]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro pos
    simp only [mem_filter, mem_univ, true_and, not_and, not_le]
    intro _
    have hu_lt : ∀ i, (u i).val < threshold := by
      intro i; by_contra h_ge; push_neg at h_ge
      have : i ∈ univ.filter (fun i : Fin C ↦ threshold ≤ (u i).val) :=
        mem_filter.mpr ⟨mem_univ _, h_ge⟩
      exact absurd (Finset.card_pos.mpr ⟨i, this⟩) (by omega)
    have hmem : net.exec u pos ∈ Set.range u := by
      rw [← net.exec_range_eq u]; exact Set.mem_range_self pos
    obtain ⟨i, hi⟩ := hmem
    calc (net.exec u pos).val = (u i).val := by rw [← hi]
      _ < threshold := hu_lt i
  -- Decompose u = g ∘ σ
  obtain ⟨g, σ, hg_strict, hu_eq, hexec, hcount⟩ := injective_monotone_perm_decomp net u hu
  have ha_eq : a = (univ.filter (fun r : Fin C ↦ threshold ≤ (g r).val)).card :=
    hcount (fun v ↦ threshold ≤ v.val)
  -- Reverse threshold: threshold ≤ (g r).val ↔ C - a ≤ r.val
  have hthresh : ∀ r : Fin C, threshold ≤ (g r).val ↔ C - a ≤ r.val := by
    rw [ha_eq]; exact strictMono_reverse_threshold hg_strict threshold
  -- Rewrite filter using threshold
  have hfilter_eq : univ.filter (fun pos : Fin C ↦
      pos.val < boundary ∧ threshold ≤ (net.exec u pos).val) =
    univ.filter (fun pos : Fin C ↦
      pos.val < boundary ∧ C - a ≤ (net.exec (⇑σ) pos).val) := by
    ext pos; simp only [mem_filter, mem_univ, true_and]
    exact and_congr_right fun _ ↦ by
      have := congr_fun hexec pos; simp only [Function.comp] at this; rw [this]; exact hthresh _
  rw [hfilter_eq]
  -- Apply SepFinal with γ' = a / C (dual ordering translation)
  have hsep := (hnet σ).2
  have hγ'_le : (a : ℝ) / ↑C ≤ γ := by
    have h1 : (a : ℝ) ≤ ⌊γ * ↑C⌋₊ := by exact_mod_cast ha
    have h2 : (⌊γ * ↑C⌋₊ : ℝ) ≤ γ * ↑C := Nat.floor_le (mul_nonneg hγ (Nat.cast_nonneg _))
    by_cases hC0 : C = 0
    · simp [hC0, hγ]
    · have hC_pos : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC0
      have hab : (a : ℝ) ≤ γ * ↑C := h1.trans h2
      calc (a : ℝ) / ↑C ≤ (γ * ↑C) / ↑C :=
          div_le_div_of_nonneg_right hab (le_of_lt hC_pos)
        _ = γ := by field_simp
  have hγ'_nn : 0 ≤ (a : ℝ) / ↑C := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hC0 : C = 0
  · -- C = 0 means m = 0, Fin 0 is empty, a = 0, contradicting ha0
    have hm0 : m = 0 := by omega
    subst hm0; exact absurd rfl ha0
  have hC_pos : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC0
  -- Apply SepFinal with γ' = a/C
  have hsep_app := hsep ((a : ℝ) / ↑C) hγ'_nn hγ'_le
  simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od, rank_fin_od_fin] at hsep_app
  -- Need: ⌊(a / C) * C⌋₊ = a
  have hfloor_a : ⌊(a : ℝ) / ↑C * ↑C⌋₊ = a := by
    rw [div_mul_cancel₀ _ (ne_of_gt hC_pos)]
    exact Nat.floor_natCast a
  rw [hfloor_a] at hsep_app
  have hbound : ε * ((a : ℝ) / ↑C) * ↑C = ε * ↑a := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hC_pos)]
  rw [hbound] at hsep_app
  -- Translate from rank/dual form to val form via ofDual/toDual bijection
  have hfilter_eq_card : (Finset.univ.filter (fun pos : Fin C ↦
      pos.val < boundary ∧ C - a ≤ (net.exec ⇑σ pos).val)).card =
    (Finset.univ.filter (fun pos : (Fin C)ᵒᵈ ↦
      ⌊γ * ↑(2 * m)⌋₊ ≤ 2 * m - 1 - pos.val ∧
      2 * m - 1 - ((net.exec ⇑σ) pos).val < a)).card := by
    apply Finset.card_nbij' (fun pos ↦ OrderDual.toDual pos) (fun pos ↦ OrderDual.ofDual pos)
    · intro pos hp
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hpv : (OrderDual.toDual pos).val = pos.val := rfl
      have hov : ((net.exec ⇑σ) (OrderDual.toDual pos)).val = (net.exec ⇑σ pos).val := rfl
      have hCm : C = 2 * m := rfl; have hfl : ⌊γ * ↑C⌋₊ = ⌊γ * ↑(2 * m)⌋₊ := rfl
      have := pos.isLt; have := (net.exec ⇑σ pos).isLt; constructor <;> omega
    · intro pos hp
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hpv : (OrderDual.ofDual pos).val = pos.val := rfl
      have hov : ((net.exec ⇑σ) (OrderDual.ofDual pos)).val = ((net.exec ⇑σ) pos).val := rfl
      have hCm : C = 2 * m := rfl; have hfl : ⌊γ * ↑C⌋₊ = ⌊γ * ↑(2 * m)⌋₊ := rfl
      have := pos.isLt; have : ((net.exec ⇑σ) pos).val < C := Fin.isLt _; constructor <;> omega
    · intro _ _; rfl
    · intro _ _; rfl
  calc ((Finset.univ.filter (fun pos : Fin C ↦
        pos.val < boundary ∧ C - a ≤ (net.exec (⇑σ) pos).val)).card : ℝ)
      = _ := by exact_mod_cast hfilter_eq_card
    _ ≤ ε * ↑a := hsep_app

/-- Stage execution on a bag's registers acts like that bag's separator.

    The stage network is a concatenation of scatter-embedded separators for all bags.
    By disjointness of register sets, only bag c's separator affects c's registers.

    This lemma connects global execution to the local separator view:
    - `r` is a position in c's registers (global Fin 2^k coordinate)
    - `i` is the local position (Fin C where C = c.regs.card)
    - The stage maps `r ↦ (c's separator).exec (perm_t ∘ embed) i` where embed(i) = r

    **Proof status:** proved below; the original plan relied on concatenation lemmas for scatter-embedded networks.
    Requires showing that executing a flatMap of disjoint scatter-embedded networks
    equals executing each individually on its own register set. -/
theorem stage_exec_on_regs (p : Params) (k : ℕ)
    (pl : Placement k) (t : ℕ) (c : Bag k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (r : Fin (2 ^ k)) (hr : r ∈ pl.regs c) :
    let regs := pl.regs c
    let C := regs.card
    let embed := regs.orderEmbOfFin rfl
    let γₑ := effectiveGamma p.γ (capacity p k t c.l) (2 * (C / 2))
    let sep := (separatorNet γₑ p.ε
      (effectiveGamma_pos p.hγ_pos (capacity_pos p k t c.l) (2 * (C / 2)))
      p.hε_pos (C / 2)).scatterEmbed (2 ^ k)
      ((Fin.castLEOrderEmb (by omega : 2 * (C / 2) ≤ C)).trans embed)
    (stage p pl t).net.exec perm r = sep.exec perm r := by
  intro regs C embed γₑ sep
  -- Step 1: Unfold stage definition
  -- (stage p pl t).net = ⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩
  -- where built b uses separateAndSplit with effectiveGamma for each bag
  -- and (built b).net is the scatter-embedded separator for bag b.
  set built := fun b : Bag k ↦
    separateAndSplit (effectiveGamma p.γ (capacity p k t b.l) (2 * ((pl.regs b).card / 2))) p.ε
      (effectiveGamma_pos p.hγ_pos (capacity_pos p k t b.l) _) p.hε_pos
      (pl.regs b) (fringe p k t b.l (pl.regs b).card)
  have hnet : (stage p pl t).net = ⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩ := by
    unfold stage
    simp only [built, separateAndSplit, separate, Build.net_bind, Build.net_emit, Build.net_pure,
      List.append_nil]

  -- Step 2: Use exec_flatMap to convert to a fold
  rw [hnet, ComparatorNetwork.exec_flatMap]

  -- Step 3: Key disjointness property
  -- For b ≠ c, pl.disjoint gives r ∉ range(embed_b), so b's network doesn't touch r
  have hdisj : ∀ b : Bag k, b ≠ c →
      ∀ c' ∈ (built b).net.comparators, r ≠ c'.i ∧ r ≠ c'.j := by
    intro b hne c' hc'
    -- b's network is scatter-embedded using (pl.regs b).orderEmbOfFin
    -- r ∈ pl.regs c, but pl.regs b and pl.regs c are disjoint
    -- So r ∉ range of b's embedding, hence c' doesn't touch r
    have hrdisj : r ∉ pl.regs b := by
      intro hr'
      exact disjoint_left.mp (pl.disjoint c b (Ne.symm hne)) hr hr'
    -- (built b).net is scatter-embedded using (pl.regs b).orderEmbOfFin
    -- r ∉ pl.regs b = range of embedding, so scatterEmbed_comparators_outside applies
    simp only [built, separateAndSplit, separate, Build.net_bind, Build.net_emit,
      Build.net_pure, List.append_nil] at hc'
    have hrange : r ∉ Set.range ((Fin.castLEOrderEmb
        (by omega : 2 * ((pl.regs b).card / 2) ≤ (pl.regs b).card)).trans
        ((pl.regs b).orderEmbOfFin rfl)) := by
      intro ⟨i, hi⟩; apply hrdisj; rw [← hi]; exact orderEmbOfFin_mem _ rfl _
    exact ComparatorNetwork.scatterEmbed_comparators_outside _ _ _ r hrange c' hc'

  -- Step 4: Stronger disjointness - bags b ≠ c don't touch ANY position in c's regs
  have hdisj_full : ∀ b : Bag k, b ≠ c → ∀ s ∈ regs,
      ∀ c' ∈ (built b).net.comparators, s ≠ c'.i ∧ s ≠ c'.j := by
    intro b hne s hs c' hc'
    have hsdisj : s ∉ pl.regs b := by
      intro hs'
      exact disjoint_left.mp (pl.disjoint c b (Ne.symm hne)) hs hs'
    simp only [built, separateAndSplit, separate, Build.net_bind, Build.net_emit,
      Build.net_pure, List.append_nil] at hc'
    have hrange : s ∉ Set.range ((Fin.castLEOrderEmb
        (by omega : 2 * ((pl.regs b).card / 2) ≤ (pl.regs b).card)).trans
        ((pl.regs b).orderEmbOfFin rfl)) := by
      intro ⟨i, hi⟩; apply hsdisj; rw [← hi]; exact orderEmbOfFin_mem _ rfl _
    exact ComparatorNetwork.scatterEmbed_comparators_outside _ _ _ s hrange c' hc'

  -- Step 5: The fold at r equals c's network applied to perm
  -- Key insight: bags b ≠ c don't modify ANY position in c's registers
  -- So when we reach c, the accumulated values at c's registers equal perm
  -- After c processes r, subsequent bags don't modify r (by hdisj)

  -- (built c).net = sep (the scatter-embedded separator)
  have hbuilt_c : (built c).net = sep := by
    simp only [built, separateAndSplit, separate, Build.net_bind, Build.net_emit, Build.net_pure,
      sep, List.append_nil]; rfl

  -- The embedding for c's scatter embed
  set embed' : Fin (2 * (C / 2)) ↪o Fin (2 ^ k) :=
    (Fin.castLEOrderEmb (by omega : 2 * (C / 2) ≤ C)).trans embed with hembed'_def

  -- embed' maps into regs
  have hembed'_mem : ∀ i : Fin (2 * (C / 2)), embed' i ∈ regs := by
    intro i; exact orderEmbOfFin_mem _ rfl _

  -- Helper: if v agrees with perm on c's regs, (built c).net.exec v = (built c).net.exec perm on c's regs
  have hc_indep : ∀ v : Fin (2 ^ k) → Fin (2 ^ k),
      (∀ s ∈ regs, v s = perm s) →
      ∀ s ∈ regs, (built c).net.exec v s = (built c).net.exec perm s := by
    intro v hv s hs
    rw [hbuilt_c]
    by_cases hmem : s ∈ Set.range embed'
    · -- s is in range of scatter embedding: use scatterEmbed_exec_inside
      obtain ⟨i, rfl⟩ := hmem
      rw [ComparatorNetwork.scatterEmbed_exec_inside, ComparatorNetwork.scatterEmbed_exec_inside]
      congr 1
      funext j
      exact hv _ (hembed'_mem j)
    · -- s is outside range: scatter embed doesn't touch it
      rw [ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ hmem,
          ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ hmem]
      exact hv s hs

  have hfold : (allBags k).foldl (fun v' b ↦ (built b).net.exec v') perm r =
               (built c).net.exec perm r := by
    -- Split allBags at c
    obtain ⟨before, after, hxs⟩ := List.append_of_mem c.mem_allBags
    rw [hxs, List.foldl_append, List.foldl_cons]
    -- Extract disjointness from nodup
    have hnd := allBags_nodup (k := k)
    rw [hxs, List.nodup_append] at hnd
    obtain ⟨_, hnd_ca, hne_ba⟩ := hnd
    have hc_notin_before : ∀ b ∈ before, b ≠ c :=
      fun b hb ↦ hne_ba b hb c List.mem_cons_self
    have hc_notin_after : ∀ b ∈ after, b ≠ c := by
      intro b hb heq; subst heq
      exact ((List.nodup_cons.mp hnd_ca).1 hb).elim
    -- Bags before c preserve perm on regs
    have hbefore_eq : ∀ s ∈ regs,
        before.foldl (fun v' b ↦ (built b).net.exec v') perm s = perm s :=
      ComparatorNetwork.foldl_exec_outside_set before (fun b ↦ (built b).net) perm regs
        (fun b hb s hs c' hc' ↦ hdisj_full b (hc_notin_before b hb) s hs c' hc')
    -- hc_indep: (built c) on the accumulated state equals (built c) on perm at regs
    have hc_step := hc_indep _ hbefore_eq r hr
    -- Bags after c don't touch r
    have hafter_eq : after.foldl (fun v' b ↦ (built b).net.exec v')
        ((built c).net.exec (before.foldl (fun v' b ↦ (built b).net.exec v') perm)) r =
        ((built c).net.exec (before.foldl (fun v' b ↦ (built b).net.exec v') perm)) r :=
      ComparatorNetwork.foldl_exec_outside after (fun b ↦ (built b).net) _ r
        (fun b hb ↦ hdisj b (hc_notin_after b hb))
    rw [hafter_eq, hc_step]

  -- Step 6: Combine
  rw [hfold, hbuilt_c]

/-- Separator filters strangers by factor ε (tight bound under IH).

    When the inductive hypothesis gives `T ≤ threshold`, the separator filtering
    lemma from Seiferas (2009) Section 5 gives: strangers in middle ≤ ε × T.

    This is TIGHTER than `separatorMiddleBound`:
    - `separatorMiddleBound ≈ min(L, εThresh) + min(H, εThresh)` (can be as large as 2·εThresh)
    - This lemma gives `ε × (L + H) = ε × T` (smaller when T ≤ threshold)

    The bound follows from `separator_injective_initial` and `separator_injective_final`:
    - Low strangers (value < anc.lo) in middle ≤ ε × L
    - High strangers (value ≥ anc.hi) in middle ≤ ε × H
    - Total: ε × (L + H) = ε × T

    **Proof status:** proved below; the original plan relied on `stage_exec_on_regs` infrastructure.

    Empirically verified: rust/test-stranger-bound.rs with 0 violations.

    **Hypothesis `hT_le`**: The stranger count must fit in the separator boundary
    `⌊γ * capacity⌋₊`. Per Seiferas (2009) p.7: "Our kick-back numbers were based on
    capacity, but our bags may not have been full to capacity." The separator works
    for effective λ' = boundary/bagCard ≥ γ when bagCard ≤ capacity.

    From the IH: strangers ≤ γ * ε^(j-1) * capacity ≤ γ * capacity = ⌊γ * capacity⌋₊. -/
theorem separator_filter_strangers (p : Params) (k : ℕ)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ) (c : Bag k) (j : ℕ) (hj : 1 ≤ j)
    (S : Finset (Fin (2 ^ k)))
    (hS_mid : let regs := (stages p k t).value.regs c
              let f := fringe p k t c.l regs.card
              S ⊆ (split regs f).toLeft ∪ (split regs f).toRight)
    (hT_le : let perm_t := (stages p k t).net.exec perm₀
             let regs := (stages p k t).value.regs c
             c.strangers j perm_t regs ≤ ⌊p.γ * capacity p k t c.l⌋₊) :
    let regs := (stages p k t).value.regs c
    let perm_t := (stages p k t).net.exec perm₀
    let perm_t1 := (stages p k (t + 1)).net.exec perm₀
    (c.strangers j perm_t1 S : ℚ) ≤ p.ε * ↑(c.strangers j perm_t regs) := by
  intro regs perm_t perm_t1

  by_cases hj0 : j = 0
  · omega
  have hj1 : j ≥ 1 := Nat.one_le_iff_ne_zero.mpr hj0
  have hj_eq : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  let anc := c.ancestor (j - 1)
  let pl := (stages p k t).value
  let C := regs.card
  let embed : Fin C ↪o Fin (2 ^ k) := regs.orderEmbOfFin rfl

  have hstrange_iff : ∀ (perm' : Fin (2 ^ k) → Fin (2 ^ k)) r, c.Strange j r perm' ↔
      (perm' r).val < anc.lo ∨ (perm' r).val ≥ anc.hi := by
    intro perm' r
    simp only [Bag.Strange, hj0, false_or]
    rw [Bag.native_iff]
    rw [not_and_or]
    simp only [Nat.not_le, Nat.not_lt]; rfl

  let lowS := S.filter (fun r ↦ (perm_t1 r).val < anc.lo)
  let highS := S.filter (fun r ↦ (perm_t1 r).val ≥ anc.hi)
  let lowRegs := regs.filter (fun r ↦ (perm_t r).val < anc.lo)
  let highRegs := regs.filter (fun r ↦ (perm_t r).val ≥ anc.hi)
  have hsub : S.filter (fun r ↦ c.Strange j r perm_t1) ⊆ lowS ∪ highS := by
    intro r hr
    rw [mem_filter] at hr
    rw [hstrange_iff perm_t1] at hr
    rw [mem_union]
    rcases hr.2 with h | h
    · exact Or.inl (mem_filter.mpr ⟨hr.1, h⟩)
    · exact Or.inr (mem_filter.mpr ⟨hr.1, h⟩)

  -- Bound: strangers in S ≤ lowS.card + highS.card
  have hbound : c.strangers j perm_t1 S ≤ lowS.card + highS.card := by
    simp only [Bag.strangers]
    calc (S.filter (fun r ↦ c.Strange j r perm_t1)).card
        ≤ (lowS ∪ highS).card := Finset.card_le_card hsub
      _ ≤ lowS.card + highS.card := Finset.card_union_le _ _

  -- Similarly for strangers in regs
  have hstrangers_regs : c.strangers j perm_t regs =
      (regs.filter (fun r ↦ (perm_t r).val < anc.lo ∨ (perm_t r).val ≥ anc.hi)).card := by
    simp only [Bag.strangers]
    congr 1
    ext r
    simp only [mem_filter]
    exact and_congr_right fun _ ↦ hstrange_iff perm_t r

  let f := fringe p k t c.l C
  have hsep : pl.regs c = regs := rfl
  have hC : C = (pl.regs c).card := rfl
  let u : Fin C → Fin (2 ^ k) := perm_t ∘ embed
  have hu_inj : Function.Injective u := by
    intro i₁ i₂ heq
    have hperm_t_inj : Function.Injective perm_t :=
      ComparatorNetwork.exec_injective _ hperm.1
    exact embed.injective (hperm_t_inj heq)

  let n_local := 2 * (C / 2)
  let γₑ := effectiveGamma p.γ (capacity p k t c.l) n_local
  let sep_local := separatorNet γₑ p.ε
    (effectiveGamma_pos p.hγ_pos (capacity_pos p k t c.l) n_local) p.hε_pos (C / 2)

  let boundary := ⌊p.γ * capacity p k t c.l⌋₊
  let L := (regs.filter (fun r ↦ (perm_t r).val < anc.lo)).card
  let H := (regs.filter (fun r ↦ (perm_t r).val ≥ anc.hi)).card

  have hstrangers_decomp : c.strangers j perm_t regs = L + H := by
    simp only [Bag.strangers, L, H]
    have hdisjoint : Disjoint (regs.filter (fun r ↦ (perm_t r).val < anc.lo))
                              (regs.filter (fun r ↦ (perm_t r).val ≥ anc.hi)) := by
      rw [Finset.disjoint_filter]
      intro r _ hlt hge
      exact absurd hge (Nat.not_le.mpr (Nat.lt_trans hlt anc.lo_lt_hi))
    have hunion : regs.filter (fun r ↦ c.Strange j r perm_t) =
                  (regs.filter (fun r ↦ (perm_t r).val < anc.lo)) ∪
                  (regs.filter (fun r ↦ (perm_t r).val ≥ anc.hi)) := by
      ext r
      constructor
      · intro hr
        rw [mem_filter] at hr
        rcases (hstrange_iff perm_t r).mp hr.2 with h | h
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hr.1, h⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hr.1, h⟩))
      · intro hr
        rw [mem_union] at hr
        rcases hr with hr | hr <;> rw [mem_filter] at hr
        · exact mem_filter.mpr ⟨hr.1, (hstrange_iff perm_t r).mpr (Or.inl hr.2)⟩
        · exact mem_filter.mpr ⟨hr.1, (hstrange_iff perm_t r).mpr (Or.inr hr.2)⟩
    rw [hunion, Finset.card_union_of_disjoint hdisjoint]

  have hL_le : L ≤ boundary := by
    calc L ≤ L + H := Nat.le_add_right _ _
      _ = c.strangers j perm_t regs := hstrangers_decomp.symm
      _ ≤ ⌊p.γ * capacity p k t c.l⌋₊ := hT_le

  have hH_le : H ≤ boundary := by
    calc H ≤ L + H := Nat.le_add_left _ _
      _ = c.strangers j perm_t regs := hstrangers_decomp.symm
      _ ≤ ⌊p.γ * capacity p k t c.l⌋₊ := hT_le

  -- With effectiveGamma, the boundary resolves:
  -- ⌊γₑ * n_local⌋₊ = ⌊γ * capacity⌋₊ = boundary (when n_local > 0)
  -- So a ≤ boundary in separator_injective_initial matches hT_le from IH.
  --
  -- The sub-bounds each require:
  -- 1. stage_exec_on_regs: perm_t1 = sep.exec perm_t on c's regs
  -- 2. scatterEmbed_exec_inside: connect global to local separator view
  -- 3. separator_injective_initial/final: bound low/high leakage
  -- 4. Coordinate translation between S (global) and local positions
  -- Establish perm_t1 = (stage p pl t).net.exec perm_t
  have hexec : perm_t1 = (stage p (stages p k t).value t).net.exec perm_t := by
    show (do let pl' ← stages p k t; stage p pl' t).net.exec perm₀ = _
    rw [Build.exec_bind]
  -- S ⊆ regs (since toLeft, toRight ⊆ regs)
  have hS_regs : S ⊆ regs :=
    hS_mid.trans (union_subset (split_toLeft_subset _ _) (split_toRight_subset _ _))
  -- Local embedding into first n_local positions
  set embed' : Fin n_local ↪o Fin (2 ^ k) :=
    (Fin.castLEOrderEmb (by omega : n_local ≤ C)).trans embed with hembed'_def
  set u' : Fin n_local → Fin (2 ^ k) := perm_t ∘ embed' with hu'_def
  -- u' is injective
  have hu'_inj : Function.Injective u' := by
    intro i₁ i₂ heq
    exact embed'.injective (ComparatorNetwork.exec_injective _ hperm.1 heq)
  -- embed' maps into regs
  have hembed'_mem : ∀ i : Fin n_local, embed' i ∈ regs := fun i ↦
    orderEmbOfFin_mem _ rfl _
  set f := fringe p k t c.l C with hf_def
  set h_half := C / 2 - f with hh_def
  have hperm_t1_eq : ∀ (pos : Fin n_local), embed' pos ∈ regs →
      perm_t1 (embed' pos) = sep_local.exec u' pos := by
    intro pos _
    have hstage := stage_exec_on_regs p k (stages p k t).value t c perm_t
      (embed' pos) (hembed'_mem pos)
    rw [hexec, hstage]
    exact ComparatorNetwork.scatterEmbed_exec_inside sep_local (2 ^ k) embed' perm_t pos
  set a := (Finset.univ.filter (fun i : Fin n_local ↦ (u' i).val < anc.lo)).card
    with ha_def
  have ha_le_L : a ≤ L := by
    apply Finset.card_le_card_of_injOn (fun i ↦ (embed' i : Fin (2 ^ k)))
    · intro i hi
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hembed'_mem i, hi⟩
    · intro i₁ _ i₂ _ heq
      exact embed'.injective heq
  set a_hi := (Finset.univ.filter (fun i : Fin n_local ↦
      anc.hi ≤ (u' i).val)).card with ha_hi_def
  have ha_hi_le_H : a_hi ≤ H := by
    apply Finset.card_le_card_of_injOn (fun i ↦ (embed' i : Fin (2 ^ k)))
    · intro i hi
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hembed'_mem i, hi⟩
    · intro i₁ _ i₂ _ heq
      exact embed'.injective heq
  -- Handle trivial cases before separator analysis
  by_cases hS_empty : S = ∅
  · simp only [Bag.strangers, hS_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg p.hε_pos.le (Nat.cast_nonneg _)
  have hS_nonempty : S.Nonempty := Finset.nonempty_of_ne_empty hS_empty
  -- Root: ancestor covers [0, 2^k), so lowS and highS are empty
  by_cases hcl : c.l = 0
  · have hcx0 : c.x = 0 := by have := c.hx; rw [hcl] at this; omega
    have hlo0 : anc.lo = 0 := by
      show (c.ancestor (j - 1)).lo = 0; simp [Bag.ancestor, hcl, hcx0, Bag.lo]
    have hhi_ge : 2 ^ k ≤ anc.hi := by
      show 2 ^ k ≤ (c.ancestor (j - 1)).hi; simp [Bag.ancestor, hcl, hcx0, Bag.hi, Bag.size]
    have hlowS0 : lowS = ∅ := by ext r; simp [lowS, hlo0]
    have hhighS0 : highS = ∅ := by
      ext r; simp only [highS, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _; have := (perm_t1 r).isLt; omega
    have h0 : c.strangers j perm_t1 S = 0 := Nat.eq_zero_of_le_zero (by
      calc c.strangers j perm_t1 S ≤ lowS.card + highS.card := hbound
        _ = 0 := by simp [hlowS0, hhighS0])
    simp only [h0, Nat.cast_zero]; exact mul_nonneg p.hε_pos.le (Nat.cast_nonneg _)
  -- Non-root, S nonempty: shared setup for separator analysis
  have hcl_pos : 0 < c.l := Nat.pos_of_ne_zero hcl
  have hf_lt : f < C / 2 := by
    by_contra hge; push_neg at hge
    have ⟨hl, hr⟩ := split_leaf regs f hge
    exact hS_nonempty.ne_empty (Finset.eq_empty_iff_forall_notMem.mpr fun r hr_S ↦ by
      have := hS_mid hr_S; rw [hl, hr, Finset.union_empty] at this
      exact Finset.notMem_empty _ this)
  have hfh_le : f + 2 * h_half ≤ n_local := by omega
  have hn_pos : 0 < n_local := by omega
  have hc_not_leaf : ¬(k ≤ c.l + 1) := by
    intro hle
    have : fringe p k t c.l C = C / 2 := by simp [fringe, show c.l ≠ 0 from by omega, hle]
    have : f = C / 2 := hf_def.symm ▸ this; omega
  have hf_eq : f = boundary := by
    show fringe p k t c.l C = boundary
    simp [fringe, show c.l ≠ 0 from by omega, show ¬(k ≤ c.l + 1) from hc_not_leaf]; rfl
  have hγₑ_le : γₑ ≤ 1 / 2 := by
    change effectiveGamma p.γ (capacity p k t c.l) n_local ≤ 1 / 2
    unfold effectiveGamma
    rw [if_neg (show n_local ≠ 0 from by omega)]
    rw [div_le_div_iff₀ (by exact_mod_cast hn_pos : (0 : ℚ) < ↑n_local) (by norm_num : (0 : ℚ) < 2)]
    rw [one_mul]; show p.γ * ↑(capacity p k t c.l) * 2 ≤ ↑(2 * (C / 2))
    push_cast
    have : p.γ * ↑(capacity p k t c.l) < ↑(C / 2) := by
      exact_mod_cast Nat.lt_of_floor_lt (by omega : ⌊p.γ * ↑(capacity p k t c.l)⌋₊ < C / 2)
    linarith
  have hsep_is : IsSeparator sep_local ↑γₑ ↑p.ε :=
    separatorNet_isSeparator γₑ p.ε
      (effectiveGamma_pos p.hγ_pos (capacity_pos p k t c.l) n_local)
      p.hε_pos hγₑ_le (C / 2)
  have hboundary_eq : ⌊(↑γₑ : ℝ) * ↑n_local⌋₊ = boundary := by
    have : (↑γₑ : ℝ) * ↑n_local = ↑(γₑ * ↑n_local) := by push_cast; ring
    rw [this, floor_rat_real_eq _ (mul_nonneg (le_of_lt (effectiveGamma_pos p.hγ_pos
      (capacity_pos p k t c.l) n_local)) (Nat.cast_nonneg _)),
      effectiveGamma_mul p.γ (capacity p k t c.l) (by omega : n_local ≠ 0)]
  -- Helper: any r ∈ S maps to a local Fin n_local position in the middle range
  have hmid_local : ∀ r ∈ S, ∃ pos : Fin n_local, embed' pos = r ∧
      f ≤ pos.val ∧ pos.val < f + 2 * h_half := by
    intro r hr_S
    have hr_mid := hS_mid hr_S
    rw [Finset.mem_union] at hr_mid
    obtain ⟨j, hjf, hj_lt, hj_eq⟩ : ∃ j : Fin C, f ≤ j.val ∧ j.val < f + 2 * h_half ∧
        embed j = r := by
      rcases hr_mid with hmem | hmem
      · obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hmem
        have hj_f := Finset.mem_filter.mp hj_mem
        have hjf' : f ≤ j.val := hj_f.2.1
        have hjlt' : j.val < f + h_half := hj_f.2.2
        exact ⟨j, hjf', hjlt'.trans_le (by omega), rfl⟩
      · obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hmem
        have hj_f := Finset.mem_filter.mp hj_mem
        have hjge' : f + h_half ≤ j.val := hj_f.2.1
        exact ⟨j, by omega, hj_f.2.2, rfl⟩
    set pos : Fin n_local := ⟨j.val, by omega⟩
    have hpos_eq : embed' pos = r := by
      simp only [hembed'_def, RelEmbedding.trans_apply, Fin.castLEOrderEmb_apply, Fin.castLE]
      exact congrArg embed (Fin.ext rfl) ▸ hj_eq
    exact ⟨pos, hpos_eq, hjf, hj_lt⟩
  -- Low filter: low strangers in middle ≤ ε × L
  have hlow_filter : (lowS.card : ℚ) ≤ p.ε * ↑L := by
    by_cases hlowS0 : lowS.card = 0
    · simp [hlowS0]; exact mul_nonneg (le_of_lt p.hε_pos) (Nat.cast_nonneg _)
    have ha_le_bdy : a ≤ ⌊(↑γₑ : ℝ) * ↑n_local⌋₊ := by
      rw [hboundary_eq]; exact ha_le_L.trans hL_le
    have hsep_bound := separator_injective_initial hsep_is
      (by exact_mod_cast (effectiveGamma_pos p.hγ_pos (capacity_pos p k t c.l) n_local).le :
        (0 : ℝ) ≤ ↑γₑ)
      u' hu'_inj anc.lo ha_le_bdy
    set local_filter := Finset.univ.filter (fun pos : Fin n_local ↦
      ⌊(↑γₑ : ℝ) * ↑n_local⌋₊ ≤ pos.val ∧ (sep_local.exec u' pos).val < anc.lo) with hlf
    have hlowS_le : lowS.card ≤ local_filter.card := by
      suffices h : lowS ⊆ Finset.image embed' local_filter by
        calc lowS.card ≤ (Finset.image embed' local_filter).card := Finset.card_le_card h
          _ = local_filter.card := Finset.card_image_of_injective _ embed'.injective
      intro r hr
      have ⟨hr_S, hr_val⟩ : r ∈ S ∧ (perm_t1 r).val < anc.lo := Finset.mem_filter.mp hr
      obtain ⟨pos, hpos_eq, hjf, _⟩ := hmid_local r hr_S
      exact Finset.mem_image.mpr ⟨pos, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [hboundary_eq.trans hf_eq.symm]; exact hjf, by
        rw [← hperm_t1_eq pos (by rw [hpos_eq]; exact hS_regs hr_S), hpos_eq]; exact hr_val⟩,
        hpos_eq⟩
    have hchain : (lowS.card : ℝ) ≤ (↑p.ε : ℝ) * (↑L : ℝ) :=
      calc (lowS.card : ℝ) ≤ local_filter.card := by exact_mod_cast hlowS_le
        _ ≤ (↑p.ε : ℝ) * ↑a := hsep_bound
        _ ≤ (↑p.ε : ℝ) * ↑L := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast ha_le_L)
              (by exact_mod_cast p.hε_pos.le)
    exact_mod_cast hchain
  -- High filter: high strangers in middle ≤ ε × H
  have hhigh_filter : (highS.card : ℚ) ≤ p.ε * ↑H := by
    by_cases hhighS0 : highS.card = 0
    · simp [hhighS0]; exact mul_nonneg (le_of_lt p.hε_pos) (Nat.cast_nonneg _)
    have ha_hi_le_bdy : a_hi ≤ ⌊(↑γₑ : ℝ) * ↑n_local⌋₊ := by
      rw [hboundary_eq]; exact ha_hi_le_H.trans hH_le
    have hsep_bound := separator_injective_final hsep_is
      (by exact_mod_cast (effectiveGamma_pos p.hγ_pos (capacity_pos p k t c.l) n_local).le :
        (0 : ℝ) ≤ ↑γₑ)
      u' hu'_inj anc.hi ha_hi_le_bdy
    set local_filter_hi := Finset.univ.filter (fun pos : Fin n_local ↦
      pos.val < n_local - ⌊(↑γₑ : ℝ) * ↑n_local⌋₊ ∧
      anc.hi ≤ (sep_local.exec u' pos).val) with hlf_hi
    have hhighS_le : highS.card ≤ local_filter_hi.card := by
      suffices h : highS ⊆ Finset.image embed' local_filter_hi by
        calc highS.card ≤ (Finset.image embed' local_filter_hi).card := Finset.card_le_card h
          _ = local_filter_hi.card := Finset.card_image_of_injective _ embed'.injective
      intro r hr
      have ⟨hr_S, hr_val⟩ : r ∈ S ∧ anc.hi ≤ (perm_t1 r).val := Finset.mem_filter.mp hr
      obtain ⟨pos, hpos_eq, _, hj_lt⟩ := hmid_local r hr_S
      refine Finset.mem_image.mpr ⟨pos, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
        hpos_eq⟩
      · rw [hboundary_eq.trans hf_eq.symm]; show pos.val < n_local - f; omega
      · rw [← hperm_t1_eq pos (by rw [hpos_eq]; exact hS_regs hr_S), hpos_eq]; exact hr_val
    have hchain : (highS.card : ℝ) ≤ (↑p.ε : ℝ) * (↑H : ℝ) :=
      calc (highS.card : ℝ) ≤ local_filter_hi.card := by exact_mod_cast hhighS_le
        _ ≤ (↑p.ε : ℝ) * ↑a_hi := hsep_bound
        _ ≤ (↑p.ε : ℝ) * ↑H := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast ha_hi_le_H)
              (by exact_mod_cast p.hε_pos.le)
    exact_mod_cast hchain
  -- Combine low and high bounds
  calc (c.strangers j perm_t1 S : ℚ)
      ≤ ↑(lowS.card + highS.card) := by exact_mod_cast hbound
    _ = ↑lowS.card + ↑highS.card := by push_cast; ring
    _ ≤ p.ε * ↑L + p.ε * ↑H := add_le_add hlow_filter hhigh_filter
    _ = p.ε * (↑L + ↑H) := by ring
    _ = p.ε * ↑(L + H) := by push_cast; ring
    _ = p.ε * ↑(c.strangers j perm_t regs) := by rw [hstrangers_decomp]

/-- Items received from parent: j-stranger bound for j ≥ 2.

    **Proof strategy (from Seiferas 2009 Section 5):**

    For j ≥ 2, j-strangers of bag b are (j-1)-strangers of b.parent. The key is that
    these strangers must "leak through" the separator to end up in the middle portion.

    Proof chain:
    1. Level shift: b.strangers j = parent.strangers (j-1) (Bag.strangers_parent_eq)
    2. Separator filtering: strangers in S ≤ ε × strangers in parent_regs
       (uses separator_filter_strangers)
    3. IH: parent.strangers(j-1) ≤ γ·ε^(j-2)·cap
    4. Combine: ε × γ·ε^(j-2)·cap = γ·ε^(j-1)·cap

    The "factor of 2 discrepancy" noted earlier was a misunderstanding:
    - `separatorMiddleBound` gives a worst-case bound (~2εγ·size)
    - The actual separator filtering (Seiferas's argument) gives ε × T
    - Under IH, ε × T = ε × γ·ε^(j-2)·cap = γ·ε^(j-1)·cap (exact match!)

    Empirically verified: rust/test-stranger-bound.rs, max ratio ~0.15.

    Note: `hS_mid` restricts `S` to the split's middle portion.
    The bound is false for `S = regs(b.parent)` (would need ε ≥ 1). -/
theorem parent_stranger_j2_le (p : Params) (k : ℕ)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j ((stages p k t).net.exec perm₀)
        ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l)
    (b : Bag k) (hl : 1 ≤ b.l) (j : ℕ) (hj : 2 ≤ j)
    (S : Finset (Fin (2 ^ k)))
    (hS_mid : let regs := (stages p k t).value.regs b.parent
              let f := fringe p k t b.parent.l regs.card
              S ⊆ (split regs f).toLeft ∪ (split regs f).toRight) :
    (b.strangers j ((stages p k (t + 1)).net.exec perm₀) S : ℚ) ≤
    p.γ * p.ε ^ (j - 1) * capacity p k t (b.l - 1) := by
  set parent := b.parent
  set parent_regs := (stages p k t).value.regs parent
  set perm_t := (stages p k t).net.exec perm₀
  set perm_t1 := (stages p k (t + 1)).net.exec perm₀

  have hj1 : 1 ≤ j - 1 := by omega
  have level_shift : b.strangers j perm_t1 S = parent.strangers (j - 1) perm_t1 S := by
    have heq := Bag.strangers_parent_eq b (j - 1) hj1 hl perm_t1 S
    -- heq : b.parent.strangers (j-1) perm_t1 S = b.strangers ((j-1)+1) perm_t1 S
    simp only [show j - 1 + 1 = j from by omega] at heq
    exact heq.symm

  have perm_inv := strangers_stage_invariant p k perm₀ t parent (j - 1)
  have hS_sub : S ⊆ parent_regs := by
    calc S ⊆ (split parent_regs _).toLeft ∪ (split parent_regs _).toRight := hS_mid
      _ ⊆ parent_regs := Finset.union_subset (split_toLeft_subset _ _) (split_toRight_subset _ _)

  have hih := ih parent (j - 1) hj1
  have hparent_l : parent.l = b.l - 1 := rfl

  -- Separator filtering: strangers in S ≤ ε × strangers in parent_regs at t
  -- Need hT_le: strangers ≤ ⌊γ * capacity⌋₊ (from IH + ε^(j-2) ≤ 1)
  have hT_le : parent.strangers (j - 1) perm_t parent_regs ≤ ⌊p.γ * capacity p k t parent.l⌋₊ := by
    have hih' := ih parent (j - 1) hj1
    -- ε^(j-2) ≤ 1 since ε ≤ 1
    have hε_pow_le : p.ε ^ (j - 2) ≤ 1 := by
      apply pow_le_one₀ p.hε_pos.le p.hε_lt.le
    -- γ * ε^(j-2) * capacity ≤ γ * capacity
    have h1 : p.γ * p.ε ^ (j - 2) * capacity p k t parent.l ≤ p.γ * capacity p k t parent.l := by
      calc p.γ * p.ε ^ (j - 2) * capacity p k t parent.l
          = p.γ * (p.ε ^ (j - 2) * capacity p k t parent.l) := by ring
        _ ≤ p.γ * (1 * capacity p k t parent.l) := by
            apply mul_le_mul_of_nonneg_left _ p.hγ_pos.le
            apply mul_le_mul_of_nonneg_right hε_pow_le
            exact capacity_nonneg p k t parent.l
        _ = p.γ * capacity p k t parent.l := by ring
    calc parent.strangers (j - 1) perm_t parent_regs
        ≤ ⌊p.γ * p.ε ^ (j - 1 - 1) * capacity p k t parent.l⌋₊ := Nat.le_floor hih'
      _ ≤ ⌊p.γ * capacity p k t parent.l⌋₊ := Nat.floor_le_floor h1

  have hsep_filter : (parent.strangers (j - 1) perm_t1 S : ℚ) ≤
      p.ε * ↑(parent.strangers (j - 1) perm_t parent_regs) :=
    separator_filter_strangers p k perm₀ hperm t parent (j - 1) hj1 S hS_mid hT_le

  -- Chain the bounds using separator filtering
  calc (b.strangers j perm_t1 S : ℚ)
      = ↑(parent.strangers (j - 1) perm_t1 S) := by rw [level_shift]
    _ ≤ p.ε * ↑(parent.strangers (j - 1) perm_t parent_regs) := hsep_filter
    _ ≤ p.ε * (p.γ * p.ε ^ (j - 1 - 1) * capacity p k t parent.l) := by
        apply mul_le_mul_of_nonneg_left hih p.hε_pos.le
    _ = p.ε * (p.γ * p.ε ^ (j - 1 - 1) * capacity p k t (b.l - 1)) := by rw [hparent_l]
    _ = p.γ * p.ε ^ (j - 1) * capacity p k t (b.l - 1) := by
        rw [show p.ε ^ (j - 1) = p.ε * p.ε ^ (j - 1 - 1) by rw [← pow_succ']; congr 1; omega]
        ring

/-- Assembly algebra: factor `ε·(cap/(2A)) + coeff·cap = combined·cap` -/
theorem source3_assembly_algebra (ε A γ cap : ℚ) (hA : 1 < A)
    (h2εA : (2 * ε * A) ^ 2 < 1) :
    ε * (cap / (2 * A)) + (2 * γ * ε * A / (1 - (2 * ε * A) ^ 2) +
      1 / (8 * A ^ 3 - 2 * A) + γ / A + 1 / (8 * A ^ 3 - 2 * A)) * cap =
    (ε / (2 * A) + 2 * γ * ε * A / (1 - (2 * ε * A) ^ 2) +
      1 / (8 * A ^ 3 - 2 * A) + γ / A + 1 / (8 * A ^ 3 - 2 * A)) * cap := by
  have h2A : (2 : ℚ) * A ≠ 0 := by positivity
  have hD2 : (1 : ℚ) - (2 * ε * A) ^ 2 ≠ 0 := ne_of_gt (by linarith)
  have hD3 : (8 : ℚ) * A ^ 3 - 2 * A ≠ 0 := by
    have hA1 : 1 ≤ A := hA.le
    have hAcube : A ≤ A ^ 3 := by nlinarith [sq_nonneg (A - 1)]
    intro h; linarith
  field_simp
  ring

/-- Given `source3 ≤ half_D - (1-ε)·a` with `b_native ≤ a` and `b_native ≤ half_D`,
    derive `source3 ≤ ε·half_D + max(0, half_D - b_native)`. -/
theorem source3_hard_case_tail
    (ε : ℝ) (hε_nn : 0 ≤ ε) (hε_lt : ε < 1)
    (source3_card half_D b_native a : ℕ)
    (key : (source3_card : ℝ) ≤ ↑half_D - (1 - ε) * ↑a)
    (hbn_le : b_native ≤ a) (hbn_le_hD : b_native ≤ half_D) :
    (source3_card : ℝ) ≤ ε * ↑half_D + max 0 ((↑half_D : ℝ) - ↑b_native) := by
  have h1 : (1 - ε) * ↑b_native ≤ (1 - ε) * ↑a :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hbn_le) (by linarith)
  have h2 : (↑b_native : ℝ) ≤ ↑half_D := by exact_mod_cast hbn_le_hD
  calc (source3_card : ℝ) ≤ ↑half_D - (1 - ε) * ↑a := key
    _ ≤ ↑half_D - (1 - ε) * ↑b_native := by linarith
    _ = ε * ↑b_native + ((↑half_D : ℝ) - ↑b_native) := by ring
    _ ≤ ε * ↑half_D + ((↑half_D : ℝ) - ↑b_native) := by
        linarith [mul_le_mul_of_nonneg_left h2 hε_nn]
    _ ≤ ε * ↑half_D + max 0 ((↑half_D : ℝ) - ↑b_native) := by
        linarith [le_max_right (0 : ℝ) ((↑half_D : ℝ) - ↑b_native)]

/-- In `Fin (2*m)`, the lower half `{pos | pos.val < m}` has exactly `m` elements. -/
theorem fin_double_card_lt (m : ℕ) :
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m)).card = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have heq : (Finset.univ.filter (fun pos : Fin (2 * m) ↦ pos.val < m)) =
        (Finset.univ.image (fun i : Fin m ↦ (⟨i.val, by omega⟩ : Fin (2 * m)))) := by
      ext pos; constructor
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Finset.mem_image.mpr ⟨⟨pos.val, hp⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro hp
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
    rw [heq, Finset.card_image_of_injective]
    · simp
    · intro a b h; simp only [Fin.mk.injEq] at h; exact Fin.ext h

/-- In `Fin (2*m)`, the upper half `{pos | m ≤ pos.val}` has exactly `m` elements. -/
theorem fin_double_card_ge (m : ℕ) :
    (Finset.univ.filter (fun pos : Fin (2 * m) ↦ m ≤ pos.val)).card = m := by
  have := fin_double_card_lt m
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun pos : Fin (2 * m) ↦ pos.val < m)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  simp only [not_lt] at hsplit; omega

/-- Complement counting: derive `source3 ≤ half_D - (1-ε)·a` from four card equalities/bounds.
    Used by both LEFT and RIGHT child hard cases. -/
theorem complement_counting_bound
    (ε : ℝ) (source3_card same same_opp other : ℕ) (half_D a : ℕ)
    (hsrc : source3_card ≤ same)
    (hpart : same + same_opp = half_D)
    (hcount : same_opp + other = a)
    (hsep : (other : ℝ) ≤ ε * ↑a) :
    (source3_card : ℝ) ≤ ↑half_D - (1 - ε) * ↑a := by
  have hR1 : (↑same : ℝ) + ↑same_opp = ↑half_D := by exact_mod_cast hpart
  have hR2 : (↑same_opp : ℝ) + ↑other = ↑a := by exact_mod_cast hcount
  have hR3 : (↑source3_card : ℝ) ≤ ↑same := by exact_mod_cast hsrc
  linarith

/-- RIGHT child hard case: complement argument for source3 bound.
    Factored out to stay within heartbeat budget. -/
theorem right_child_hard_case
    {n_local half_D : ℕ} (hn : n_local = 2 * half_D)
    (ε : ℚ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (sep_local : ComparatorNetwork n_local) (u' : Fin n_local → Fin (2 ^ k))
    (thr : ℕ)  -- sibling.hi
    (source3_card : ℕ)
    (b_native _a_below a_above : ℕ)
    (hsrc3_le : source3_card ≤ (univ.filter (fun pos : Fin n_local ↦
        half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < thr)).card)
    (hbn_le : b_native ≤ a_above)
    (ha_above_lt : a_above < half_D)
    (ha_above_eq : a_above = (univ.filter (fun i : Fin n_local ↦ thr ≤ (u' i).val)).card)
    (hcount : ∀ (P : Fin (2 ^ k) → Prop) [DecidablePred P],
        (univ.filter (fun pos ↦ P (sep_local.exec u' pos))).card =
        (univ.filter (fun i ↦ P (u' i))).card)
    (hsep_final_bound : ∀ (t : ℕ),
        (univ.filter (fun i ↦ t ≤ (u' i).val)).card ≤ half_D →
        (↑(univ.filter (fun pos ↦ pos.val < half_D ∧ t ≤ (sep_local.exec u' pos).val)).card : ℝ) ≤
        ↑ε * ↑(univ.filter (fun i ↦ t ≤ (u' i).val)).card) :
    (source3_card : ℝ) ≤ ↑ε * ↑half_D + max 0 ((↑half_D : ℝ) - ↑b_native) := by
  subst hn
  have ha_above_le : (univ.filter (fun i : Fin (2 * half_D) ↦ thr ≤ (u' i).val)).card ≤ half_D := by
    omega
  have hsep_compl := hsep_final_bound thr ha_above_le
  have hcard_hi : (univ.filter (fun pos : Fin (2 * half_D) ↦ half_D ≤ pos.val)).card = half_D :=
    fin_double_card_ge half_D
  have hpart_hi : (univ.filter (fun pos : Fin (2 * half_D) ↦ half_D ≤ pos.val ∧
        (sep_local.exec u' pos).val < thr)).card +
      (univ.filter (fun pos : Fin (2 * half_D) ↦ half_D ≤ pos.val ∧
        thr ≤ (sep_local.exec u' pos).val)).card = half_D := by
    have hsplit := card_filter_add_card_filter_not
      (s := univ.filter (fun pos : Fin (2 * half_D) ↦ half_D ≤ pos.val))
      (fun pos ↦ (sep_local.exec u' pos).val < thr)
    simp only [Finset.filter_filter, not_lt] at hsplit
    rw [hcard_hi] at hsplit; linarith
  have hcount_hi : (univ.filter (fun pos : Fin (2 * half_D) ↦ half_D ≤ pos.val ∧
        thr ≤ (sep_local.exec u' pos).val)).card +
      (univ.filter (fun pos : Fin (2 * half_D) ↦ pos.val < half_D ∧
        thr ≤ (sep_local.exec u' pos).val)).card = a_above := by
    rw [ha_above_eq, ← hcount (fun v ↦ thr ≤ v.val)]
    have hsplit' := card_filter_add_card_filter_not
      (s := univ.filter (fun pos : Fin (2 * half_D) ↦ thr ≤ (sep_local.exec u' pos).val))
      (fun pos ↦ half_D ≤ pos.val)
    simp only [Finset.filter_filter, not_le] at hsplit'
    have h1 : (univ.filter (fun pos : Fin (2 * half_D) ↦ thr ≤
        (sep_local.exec u' pos).val ∧ half_D ≤ pos.val)) = (univ.filter (fun pos :
        Fin (2 * half_D) ↦ half_D ≤ pos.val ∧ thr ≤ (sep_local.exec u' pos).val)) := by
      ext pos; simp only [mem_filter, mem_univ, true_and]; tauto
    have h2 : (univ.filter (fun pos : Fin (2 * half_D) ↦ thr ≤
        (sep_local.exec u' pos).val ∧ pos.val < half_D)) = (univ.filter (fun pos :
        Fin (2 * half_D) ↦ pos.val < half_D ∧ thr ≤ (sep_local.exec u' pos).val)) := by
      ext pos; simp only [mem_filter, mem_univ, true_and]; tauto
    rw [h1, h2] at hsplit'; linarith
  have key : (source3_card : ℝ) ≤ ↑half_D - (1 - ↑ε) * ↑a_above :=
    complement_counting_bound (ε := ↑ε) (hsrc := hsrc3_le)
      (hpart := hpart_hi) (hcount := hcount_hi) (hsep := by
      have h1 := hsep_compl; rw [← ha_above_eq] at h1; exact_mod_cast h1)
  exact source3_hard_case_tail ↑ε (by exact_mod_cast hε_pos.le)
    (by exact_mod_cast hε_lt) _ _ _ _ key hbn_le (hbn_le.trans ha_above_lt.le)

/-- Odd-indexed partial geometric sum ≤ closed form: `Σ_{i<n} r^(2i+1) ≤ r/(1-r²)`. -/
theorem odd_geom_sum_le (r : ℚ) (hr : 0 < r) (hr2 : r ^ 2 < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ (2 * i + 1) ≤ r / (1 - r ^ 2) := by
  have h1 : ∑ i ∈ Finset.range n, r ^ (2 * i + 1) =
      r * ∑ i ∈ Finset.range n, (r ^ 2) ^ i := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [← pow_mul, mul_comm 2 i, ← pow_succ']
  rw [h1]
  have hr2_ne1 : r ^ 2 ≠ 1 := ne_of_lt hr2
  rw [geom_sum_eq hr2_ne1]
  have h_denom_pos : (0 : ℚ) < 1 - r ^ 2 := by linarith
  have h_neg : ((r ^ 2) ^ n - 1) / (r ^ 2 - 1) = (1 - (r ^ 2) ^ n) / (1 - r ^ 2) := by
    have : r ^ 2 - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [h_neg, mul_div_assoc']
  exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg (sq_nonneg r) n]) h_denom_pos.le

end


