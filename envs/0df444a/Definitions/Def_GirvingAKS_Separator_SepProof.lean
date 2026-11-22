-- Prove2me | Definitions.Def_GirvingAKS_Separator_SepProof
-- name    : GirvingAKS_Separator_SepProof
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:52:23.338372+00:00
-- url     : https://prove2.me/theorems/3b8b6cba-df28-49ae-b7f5-d8f73f117d03
-- title:
--   AKS sorting networks (Seiferas port) — Separator Correctness Proof
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Separator/SepProof.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves `separatorNet_isSeparator`: the prefix-doubling separator construction from `General.lean` satisfies `IsSeparator γ ε` for any `0 < γ ≤ 1/2` and `0 < ε` (Seiferas 2009, Section 6, Lemma 2).
--
--   Proof by induction on prefix-doubling levels (see `docs/even-separators-plan.md`).
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Separator/SepProof.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Separator_General
import Definitions.Def_GirvingAKS_Halver_Mono
import Definitions.Def_GirvingAKS_Misc_Floor

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Separator/SepProof.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Separator Correctness Proof

  Proves `separatorNet_isSeparator`: the prefix-doubling separator
  construction from `General.lean` satisfies `IsSeparator γ ε` for
  any `0 < γ ≤ 1/2` and `0 < ε` (Seiferas 2009, Section 6, Lemma 2).

  Proof by induction on prefix-doubling levels (see `docs/even-separators-plan.md`).
-/


section


open Finset BigOperators

/-! **Coverage** -/

lemma sepBaseChunk_eq_floor (γ : ℚ) (n : ℕ) (hfloor : 0 < ⌊γ * ↑n⌋₊) :
    sepBaseChunk γ n = ⌊γ * ↑n⌋₊ := by
  show max 1 ⌊γ * ↑n⌋₊ = ⌊γ * ↑n⌋₊; omega

lemma coverage_nat (γ : ℚ) (m : ℕ) (hγ : 0 < γ) :
    m ≤ 2 ^ (numSepLevels γ + 1) * sepBaseChunk γ (2 * m) := by
  have hcov := numSepLevels_coverage γ hγ
  by_cases hm : m = 0
  · subst hm; simp
  · by_cases hfloor : ⌊γ * ↑(2 * m)⌋₊ = 0
    · show m ≤ 2 ^ (numSepLevels γ + 1) * max 1 ⌊γ * ↑(2 * m)⌋₊
      rw [hfloor]; simp
      have hγn_lt : γ * ↑(2 * m) < 1 := by rwa [Nat.floor_eq_zero] at hfloor
      exact_mod_cast show (m : ℚ) ≤ 2 ^ (numSepLevels γ + 1) from by
        have h2m : (2 : ℚ) ^ (numSepLevels γ + 1) > ↑(2 * m) :=
          calc (2 : ℚ) ^ (numSepLevels γ + 1) ≥ 1 / γ := by rwa [ge_iff_le, div_le_iff₀ hγ]
            _ > ↑(2 * m) := by rw [gt_iff_lt, lt_div_iff₀ hγ]; linarith
        push_cast at h2m ⊢; linarith
    · have hfloor_pos : 0 < ⌊γ * ↑(2 * m)⌋₊ := Nat.pos_of_ne_zero hfloor
      show m ≤ 2 ^ (numSepLevels γ + 1) * max 1 ⌊γ * ↑(2 * m)⌋₊
      rw [show max 1 ⌊γ * ↑(2 * m)⌋₊ = ⌊γ * ↑(2 * m)⌋₊ from by omega]
      have hγn_ge1 : (1 : ℚ) ≤ γ * ↑(2 * m) := by
        have := Nat.floor_le (show (0 : ℚ) ≤ γ * ↑(2 * m) by positivity)
        linarith [show (1 : ℚ) ≤ ⌊γ * ↑(2 * m)⌋₊ from by exact_mod_cast hfloor_pos]
      have h2floor : γ * ↑(2 * m) ≤ 2 * ↑⌊γ * ↑(2 * m)⌋₊ := by
        linarith [Nat.lt_floor_add_one (γ * ↑(2 * m)),
          show (1 : ℚ) ≤ ⌊γ * ↑(2 * m)⌋₊ from by exact_mod_cast hfloor_pos]
      exact_mod_cast show (m : ℚ) ≤ 2 ^ (numSepLevels γ + 1) * ↑⌊γ * ↑(2 * m)⌋₊ from
        calc (m : ℚ) = ↑(2 * m) / 2 := by push_cast; ring
          _ ≤ 2 ^ (numSepLevels γ + 1) * (γ * ↑(2 * m)) / 2 := by
              apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ) ≤ 2)
              linarith [show (2:ℚ) ^ (numSepLevels γ + 1) * (γ * ↑(2 * m)) ≥ ↑(2 * m) from
                calc (2:ℚ) ^ (numSepLevels γ + 1) * (γ * ↑(2 * m))
                    = (2 ^ (numSepLevels γ + 1) * γ) * ↑(2 * m) := by ring
                  _ ≥ 1 * ↑(2 * m) := mul_le_mul_of_nonneg_right hcov (by positivity)
                  _ = ↑(2 * m) := by ring]
          _ ≤ 2 ^ (numSepLevels γ + 1) * (2 * ↑⌊γ * ↑(2 * m)⌋₊) / 2 := by
              apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ) ≤ 2)
              exact mul_le_mul_of_nonneg_left h2floor (by positivity)
          _ = 2 ^ (numSepLevels γ + 1) * ↑⌊γ * ↑(2 * m)⌋₊ := by ring


/-! **Displaced Count Helpers** -/

/-- Monotonicity: larger position boundary → smaller displaced count. -/
lemma displaced_boundary_mono {n : ℕ} (w : Fin n → Fin n) (B₁ B₂ threshold : ℕ)
    (h : B₁ ≤ B₂) :
    (univ.filter (fun pos : Fin n ↦ B₂ ≤ pos.val ∧ (w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦ B₁ ≤ pos.val ∧ (w pos).val < threshold)).card :=
  card_le_card (fun pos hp ↦ by
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨le_trans h hp.1, hp.2⟩)

/-- Displaced count at boundary B splits into far (≥ B₂) and near ([B, B₂)) parts. -/
lemma displaced_split {n : ℕ} (w : Fin n → Fin n) (B₁ B₂ threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦ B₁ ≤ pos.val ∧ (w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦ B₂ ≤ pos.val ∧ (w pos).val < threshold)).card +
    (univ.filter (fun pos : Fin n ↦
      B₁ ≤ pos.val ∧ pos.val < B₂ ∧ (w pos).val < threshold)).card := by
  calc _ ≤ ((univ.filter (fun pos : Fin n ↦ B₂ ≤ pos.val ∧ (w pos).val < threshold)) ∪
            (univ.filter (fun pos : Fin n ↦
              B₁ ≤ pos.val ∧ pos.val < B₂ ∧ (w pos).val < threshold))).card := by
        apply card_le_card
        intro pos hp
        simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
        by_cases hge : B₂ ≤ pos.val
        · left; exact ⟨hge, hp.2⟩
        · right; push_neg at hge; exact ⟨hp.1, hge, hp.2⟩
    _ ≤ _ := card_union_le _ _

/-- Far positions (≥ 2*halfLen) are unchanged by prefix shiftEmbed at offset 0. -/
lemma displaced_far_shiftEmbed {halfLen n : ℕ}
    (net : ComparatorNetwork (2 * halfLen))
    (h_fit : 0 + 2 * halfLen ≤ n)
    (v : Fin n → Fin n) (threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      2 * halfLen ≤ pos.val ∧
      ((net.shiftEmbed n 0 h_fit).exec v pos).val < threshold)).card =
    (univ.filter (fun pos : Fin n ↦
      2 * halfLen ≤ pos.val ∧ (v pos).val < threshold)).card := by
  congr 1; ext pos; simp only [mem_filter, mem_univ, true_and, and_congr_right_iff]
  intro hge; rw [ComparatorNetwork.shiftEmbed_exec_outside
    net n 0 h_fit v pos (Or.inr (by omega))]


/-! **Prefix Halver Near Bound** -/

/-- The prefix halver at offset 0 bounds small values in [halfLen, 2*halfLen).
    After applying halver.shiftEmbed at offset 0 to injective v:
    |{pos ∈ [halfLen, 2*halfLen) : exec(v, pos).val < threshold}| ≤ ε₀ * threshold. -/
lemma prefix_halver_near_bound (halfLen n : ℕ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (halver : ComparatorNetwork (2 * halfLen))
    (hhalver : IsEpsilonHalver halver ε₀)
    (h_fit : 0 + 2 * halfLen ≤ n)
    (v : Fin n → Fin n) (hv : Function.Injective v)
    (threshold : ℕ) (ht : threshold ≤ halfLen) :
    ((univ.filter (fun pos : Fin n ↦
      halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
      ((halver.shiftEmbed n 0 h_fit).exec v pos).val < threshold)).card : ℝ)
    ≤ ε₀ * ↑threshold := by
  set exec_v := (halver.shiftEmbed n 0 h_fit).exec v
  by_cases hhl : halfLen = 0
  · -- halfLen = 0: filter is empty
    have hempty : (univ.filter (fun pos : Fin n ↦
        halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
        (exec_v pos).val < threshold)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro _ _ ⟨_, h2, _⟩; omega
    simp only [hempty]; push_cast; exact mul_nonneg hε₀ (Nat.cast_nonneg _)
  have hhl_pos : 0 < halfLen := Nat.pos_of_ne_zero hhl
  set u : Fin (2 * halfLen) → Fin n :=
    fun j ↦ v ⟨j.val, by have := j.isLt; have := h_fit; omega⟩
  have hu : Function.Injective u := fun a b hab ↦ Fin.ext (by
    have := hv hab; simp only [Fin.mk.injEq] at this; exact this)
  set a := (univ.filter (fun i : Fin (2 * halfLen) ↦ (u i).val < threshold)).card
  have ha_le : a ≤ threshold := injective_count_lt_le u hu threshold
  have hbound := halver_injective_initial_halved hhalver hε₀ u hu threshold (ha_le.trans ht)
  -- Bridge: shiftEmbed at offset 0 acts locally
  have h_exec_val : ∀ (pos : Fin n) (hpos : pos.val < 2 * halfLen),
      (exec_v pos).val = (halver.exec u ⟨pos.val, hpos⟩).val := by
    intro pos hpos
    show ((halver.shiftEmbed n 0 h_fit).exec v pos).val = _
    have h := ComparatorNetwork.shiftEmbed_exec_inside halver n 0 h_fit v ⟨pos.val, hpos⟩
    simp only [Nat.zero_add] at h
    show ((halver.shiftEmbed n 0 h_fit).exec v ⟨pos.val, pos.isLt⟩).val = _
    rw [h]
  -- Injection from near filter (Fin n) to halver filter (Fin (2*halfLen))
  set f : Fin n → Fin (2 * halfLen) := fun pos ↦
    if h : pos.val < 2 * halfLen then ⟨pos.val, h⟩ else ⟨0, by omega⟩
  have h_card_le : (univ.filter (fun pos : Fin n ↦
      halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
      (exec_v pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin (2 * halfLen) ↦
      halfLen ≤ pos.val ∧ (halver.exec u pos).val < threshold)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro pos hp
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      simp only [f, dif_pos hp.2.1]
      exact ⟨hp.1, by rw [← h_exec_val pos hp.2.1]; exact hp.2.2⟩
    · intro a₁ ha₁ b₁ hb₁ hab
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at ha₁ hb₁
      simp only [f, dif_pos ha₁.2.1, dif_pos hb₁.2.1, Fin.mk.injEq] at hab
      exact Fin.ext hab
  calc ((univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
        (exec_v pos).val < threshold)).card : ℝ)
      ≤ ↑(univ.filter (fun pos : Fin (2 * halfLen) ↦
          halfLen ≤ pos.val ∧ (halver.exec u pos).val < threshold)).card :=
        by exact_mod_cast h_card_le
    _ ≤ ε₀ * ↑a := hbound
    _ ≤ ε₀ * ↑threshold := mul_le_mul_of_nonneg_left (by exact_mod_cast ha_le) hε₀


/-! **Inductive Displaced Bound (SepInitial direction)** -/

/-- After processing j prefix-doubling levels (from j-1 down to 0), the displaced
    count at boundary m₀ is bounded by D + j*ε₀*threshold.

    Parameters:
    - `D`: initial displaced bound at boundary 2^j*m₀
    - `hD_half`: initial halver bound at boundary n/2 (preserved through all levels)

    The key insight: suffix halvers only help SepInitial (by `exec_displaced_le`),
    and prefix halvers control the "near" part at each level. -/
lemma sep_initial_levels_bound
    (n m₀ : ℕ)
    (halverNet : (m : ℕ) → ComparatorNetwork (2 * m))
    (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (hhalver : ∀ m, IsEpsilonHalver (halverNet m) ε₀)
    (threshold : ℕ) (ht : threshold ≤ m₀)
    (j : ℕ) (w : Fin n → Fin n) (hw : Function.Injective w)
    (D : ℝ) (hD : (↑(univ.filter (fun pos : Fin n ↦
      2 ^ j * m₀ ≤ pos.val ∧ (w pos).val < threshold)).card : ℝ) ≤ D)
    (hD_half : (↑(univ.filter (fun pos : Fin n ↦
      n / 2 ≤ pos.val ∧ (w pos).val < threshold)).card : ℝ) ≤ ε₀ * ↑threshold) :
    (↑(univ.filter (fun pos : Fin n ↦
        m₀ ≤ pos.val ∧ ((⟨((List.range j).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k)⟩ : ComparatorNetwork n).exec w pos).val <
        threshold)).card : ℝ) ≤ D + ↑j * ε₀ * ↑threshold := by
  induction j generalizing w D with
  | zero =>
    simp only [pow_zero, one_mul] at hD
    simp only [List.range_zero, List.reverse_nil, List.flatMap_nil,
      Nat.cast_zero, zero_mul, add_zero, ComparatorNetwork.exec, List.foldl_nil]
    exact hD
  | succ j ih =>
    -- Decompose: levels [j, j-1, ..., 0] = level j ++ levels [j-1, ..., 0]
    have hdecomp : ((List.range (j + 1)).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k) =
      sepLevelComparators n halverNet m₀ j ++
      ((List.range j).reverse.flatMap fun k ↦ sepLevelComparators n halverNet m₀ k) := by
      rw [show List.range (j + 1) = List.range j ++ [j] from by rw [List.range_succ],
        List.reverse_append, List.flatMap_append]
      simp [List.flatMap_cons, List.flatMap_nil]
    rw [show (⟨((List.range (j+1)).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k)⟩ : ComparatorNetwork n) =
      ⟨sepLevelComparators n halverNet m₀ j ++
        ((List.range j).reverse.flatMap fun k ↦
          sepLevelComparators n halverNet m₀ k)⟩ from by
      exact congrArg _ hdecomp]
    rw [ComparatorNetwork.exec_append]
    set w₁ := (⟨sepLevelComparators n halverNet m₀ j⟩ : ComparatorNetwork n).exec w
    have hw₁ : Function.Injective w₁ := ComparatorNetwork.exec_injective _ hw
    -- hD_half propagates: level j can only decrease displaced count at n/2
    have hD_half_w₁ : (↑(univ.filter (fun pos : Fin n ↦
        n / 2 ≤ pos.val ∧ (w₁ pos).val < threshold)).card : ℝ) ≤ ε₀ * ↑threshold :=
      calc _ ≤ ↑(univ.filter (fun pos : Fin n ↦
                n / 2 ≤ pos.val ∧ (w pos).val < threshold)).card := by
              exact_mod_cast exec_displaced_le
                ⟨sepLevelComparators n halverNet m₀ j⟩ w (n/2) threshold
           _ ≤ ε₀ * ↑threshold := hD_half
    -- Step: show displaced(w₁, 2^j*m₀, t) ≤ D + ε₀*t, then apply IH
    suffices hstep : (↑(univ.filter (fun pos : Fin n ↦
        2 ^ j * m₀ ≤ pos.val ∧ (w₁ pos).val < threshold)).card : ℝ) ≤
      D + ε₀ * ↑threshold by
      have := ih w₁ hw₁ (D + ε₀ * ↑threshold) hstep hD_half_w₁
      calc _ ≤ (D + ε₀ * ↑threshold) + ↑j * ε₀ * ↑threshold := this
        _ = D + ↑(j + 1) * ε₀ * ↑threshold := by push_cast; ring
    -- Prove hstep: level j brings displaced down by one ε₀*threshold
    set halfLen := 2 ^ j * m₀ with hHL
    show (↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
      ((⟨sepLevelComparators n halverNet m₀ j⟩ : ComparatorNetwork n).exec w pos).val <
        threshold)).card : ℝ) ≤ D + ε₀ * ↑threshold
    by_cases h_prefix_fit : 0 + 2 * halfLen ≤ n
    · -- Prefix halver fits: split into far + near
      unfold sepLevelComparators
      -- Suffix only helps (exec_displaced_le)
      have h_suffix_helps : (univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
          ((⟨(if h : 0 + 2 * halfLen ≤ n then
              ((halverNet halfLen).shiftEmbed n 0 h).comparators else []) ++
            (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
              ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
            else [])⟩ : ComparatorNetwork n).exec w pos).val < threshold)).card ≤
        (univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
          ((⟨if h : 0 + 2 * halfLen ≤ n then
              ((halverNet halfLen).shiftEmbed n 0 h).comparators
            else []⟩ : ComparatorNetwork n).exec w pos).val < threshold)).card := by
        rw [ComparatorNetwork.exec_append]
        exact exec_displaced_le _ _ halfLen threshold
      calc (↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
            ((⟨(if h : 0 + 2 * halfLen ≤ n then
                ((halverNet halfLen).shiftEmbed n 0 h).comparators else []) ++
              (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
                ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
              else [])⟩ : ComparatorNetwork n).exec w pos).val < threshold)).card : ℝ)
          ≤ ↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
              ((⟨if h : 0 + 2 * halfLen ≤ n then
                  ((halverNet halfLen).shiftEmbed n 0 h).comparators
                else []⟩ : ComparatorNetwork n).exec w pos).val < threshold)).card := by
            exact_mod_cast h_suffix_helps
        _ ≤ D + ε₀ * ↑threshold := by
          -- After prefix only, split into far (≥ 2*halfLen) and near ([halfLen, 2*halfLen))
          rw [dif_pos h_prefix_fit]
          have hsplit := displaced_split
            (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w)
            halfLen (2 * halfLen) threshold
          calc (↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
              (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w pos).val <
                threshold)).card : ℝ)
              ≤ ↑((univ.filter (fun pos : Fin n ↦ 2 * halfLen ≤ pos.val ∧
                  (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w pos).val <
                    threshold)).card +
                (univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
                  (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w pos).val <
                    threshold)).card) := by exact_mod_cast hsplit
            _ = ↑(univ.filter (fun pos : Fin n ↦ 2 * halfLen ≤ pos.val ∧
                  (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w pos).val <
                    threshold)).card +
                ↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧ pos.val < 2 * halfLen ∧
                  (((halverNet halfLen).shiftEmbed n 0 h_prefix_fit).exec w pos).val <
                    threshold)).card := by push_cast; ring
            _ ≤ D + ε₀ * ↑threshold := by
              -- Far: unchanged by shiftEmbed, bounded by D
              rw [displaced_far_shiftEmbed (halverNet halfLen) h_prefix_fit w threshold]
              have h2hl : 2 * halfLen = 2 ^ (j + 1) * m₀ := by
                show 2 * (2 ^ j * m₀) = 2 ^ (j + 1) * m₀; rw [pow_succ]; ring
              have hfar : (↑(univ.filter (fun pos : Fin n ↦ 2 * halfLen ≤ pos.val ∧
                  (w pos).val < threshold)).card : ℝ) ≤ D := by
                suffices h : (univ.filter (fun pos : Fin n ↦ 2 * halfLen ≤ pos.val ∧
                    (w pos).val < threshold)) =
                  (univ.filter (fun pos : Fin n ↦ 2 ^ (j + 1) * m₀ ≤ pos.val ∧
                    (w pos).val < threshold)) by rw [h]; exact hD
                congr 1; ext pos; exact and_congr_left' (by rw [h2hl])
              have hm₀_le_hl : m₀ ≤ halfLen :=
                Nat.le_mul_of_pos_left m₀ (pow_pos (by norm_num : 0 < 2) j)
              -- Near: bounded by ε₀ * threshold
              have hnear := prefix_halver_near_bound halfLen n ε₀ hε₀
                (halverNet halfLen) (hhalver halfLen) h_prefix_fit w hw
                threshold (le_trans ht hm₀_le_hl)
              linarith
    · -- No-op case: prefix doesn't fit (2*halfLen > n)
      -- Don't unfold sepLevelComparators; use exec_displaced_le as black box
      push_neg at h_prefix_fit
      have hhl_ge : n / 2 ≤ halfLen := by omega
      calc (↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
              ((⟨sepLevelComparators n halverNet m₀ j⟩ : ComparatorNetwork n).exec w pos).val <
              threshold)).card : ℝ)
          ≤ ↑(univ.filter (fun pos : Fin n ↦ halfLen ≤ pos.val ∧
              (w pos).val < threshold)).card := by
            exact_mod_cast exec_displaced_le
              ⟨sepLevelComparators n halverNet m₀ j⟩ w halfLen threshold
        _ ≤ ↑(univ.filter (fun pos : Fin n ↦ n / 2 ≤ pos.val ∧
              (w pos).val < threshold)).card := by
            exact_mod_cast displaced_boundary_mono w (n/2) halfLen threshold hhl_ge
        _ ≤ ε₀ * ↑threshold := hD_half
        _ ≤ D + ε₀ * ↑threshold := by
            linarith [le_trans (Nat.cast_nonneg (univ.filter (fun pos : Fin n ↦
              2 ^ (j + 1) * m₀ ≤ pos.val ∧ (w pos).val < threshold)).card) hD]


/-! **SepInitial direction** -/

/-- The prefix-doubling separator satisfies `SepInitial`. -/
theorem separatorNet_sepInitial (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε)
    (hγ_le : γ ≤ 1 / 2) (m : ℕ) (v : Equiv.Perm (Fin (2 * m))) :
    SepInitial ((separatorNet γ ε hγ hε m).exec v) ↑γ ↑ε := by
  -- Trivial case: ⌊γ(2m)⌋₊ = 0
  by_cases hfloor : ⌊(γ : ℝ) * ↑(2 * m)⌋₊ = 0
  · exact sepInitial_trivial _ ↑γ ↑ε (by exact_mod_cast hε.le) (by exact_mod_cast hγ.le) hfloor
  -- Non-trivial: ⌊γ(2m)⌋₊ ≥ 1
  have hfloor_pos : 0 < ⌊(γ : ℚ) * ↑(2 * m)⌋₊ := by
    rw [(floor_rat_real_mul_nat γ (2 * m) hγ.le).symm]
    exact Nat.pos_of_ne_zero hfloor
  -- Setup
  set t := sepTotalLayers γ with ht_def
  set ε₀_Q := ε / ↑t with hε₀_Q_def
  have hε₀_Q_pos : (0 : ℚ) < ε₀_Q := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  set family := halvers ε₀_Q hε₀_Q_pos
  set m₀ := sepBaseChunk γ (2 * m) with hm₀_def
  set K := numSepLevels γ + 1 with hK_def
  have hm₀_eq : m₀ = ⌊(γ : ℚ) * ↑(2 * m)⌋₊ := sepBaseChunk_eq_floor γ (2 * m) hfloor_pos
  have hm₀_pos : 0 < m₀ := by omega
  set ε₀ : ℝ := ↑ε₀_Q with hε₀_def
  have hε₀ : (0 : ℝ) ≤ ε₀ := by show (0 : ℝ) ≤ ↑ε₀_Q; exact_mod_cast hε₀_Q_pos.le
  -- Decompose separator
  have hsep_eq : (separatorNet γ ε hγ hε m).comparators =
      (family.net m).comparators ++
      ((List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k) := by
    unfold separatorNet; rfl
  set w₀ := (family.net m).exec (v : Fin (2 * m) → Fin (2 * m))
  have hw₀_inj : Function.Injective w₀ :=
    ComparatorNetwork.exec_injective _ v.injective
  have hresult_eq : (separatorNet γ ε hγ hε m).exec (v : Fin (2 * m) → Fin (2 * m)) =
      (⟨(List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k⟩ :
        ComparatorNetwork (2 * m)).exec w₀ := by
    show (⟨(separatorNet γ ε hγ hε m).comparators⟩ : ComparatorNetwork (2 * m)).exec v = _
    rw [hsep_eq, ComparatorNetwork.exec_append]
  -- Open SepInitial, simplify rank/Fintype.card, rewrite exec and floor
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_fin, rank_fin_val]
  simp_rw [hresult_eq, floor_rat_real_mul_nat γ (2 * m) hγ.le, ← hm₀_eq]
  -- Now goal is: ↑(filter (m₀ ≤ pos.val ∧ (exec w₀ pos).val < ⌊γ'·2m⌋₊)).card ≤ ↑ε * γ' * ↑(2*m)
  set threshold := ⌊γ' * ↑(2 * m)⌋₊ with hthresh_def
  -- threshold ≤ m₀
  have ht_le_m₀ : threshold ≤ m₀ := by
    rw [hthresh_def, hm₀_eq, ← floor_rat_real_mul_nat γ (2 * m) hγ.le]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hγ'_le (Nat.cast_nonneg _))
  -- threshold ≤ m
  have ht_le_m : threshold ≤ m := by
    calc threshold ≤ ⌊(1 / 2 : ℝ) * ↑(2 * m)⌋₊ := by
          rw [hthresh_def]; apply Nat.floor_le_floor
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          calc γ' ≤ ↑γ := hγ'_le
            _ ≤ ↑(1 / 2 : ℚ) := by exact_mod_cast hγ_le
            _ = 1 / 2 := by push_cast; ring
      _ = m := by
          rw [show (1 / 2 : ℝ) * ↑(2 * m) = ↑m from by push_cast; ring]
          exact Nat.floor_natCast m
  -- Initial halver bound
  have h_perm_count : (univ.filter (fun i : Fin (2 * m) ↦
      (v i : Fin (2 * m)).val < threshold)).card = threshold := by
    rw [bijection_count_val_lt v v.injective, card_filter_val_lt (2 * m) threshold (by omega)]
  have h_init_bound : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ (w₀ pos).val < threshold)).card : ℝ) ≤ ε₀ * ↑threshold := by
    have hmain := halver_injective_initial_halved (family.isHalver m) hε₀
      (v : Fin (2 * m) → Fin (2 * m)) v.injective threshold
    have ha_le : (univ.filter (fun i : Fin (2 * m) ↦
        (v i : Fin (2 * m)).val < threshold)).card ≤ m := by
      rw [h_perm_count]; exact ht_le_m
    have h := hmain ha_le
    simp only [h_perm_count] at h
    exact h
  -- Coverage: m ≤ 2^K * m₀
  have hcov : m ≤ 2 ^ K * m₀ := coverage_nat γ m hγ
  -- displaced(w₀, 2^K*m₀, threshold) ≤ ε₀*threshold
  have hD : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      2 ^ K * m₀ ≤ pos.val ∧ (w₀ pos).val < threshold)).card : ℝ) ≤ ε₀ * ↑threshold :=
    calc _ ≤ ↑(univ.filter (fun pos : Fin (2 * m) ↦
            m ≤ pos.val ∧ (w₀ pos).val < threshold)).card := by
          exact_mod_cast displaced_boundary_mono w₀ m (2 ^ K * m₀) threshold hcov
       _ ≤ ε₀ * ↑threshold := h_init_bound
  -- hD_half: initial halver bound at boundary (2*m)/2 = m
  have hD_half : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      (2 * m) / 2 ≤ pos.val ∧ (w₀ pos).val < threshold)).card : ℝ) ≤ ε₀ * ↑threshold := by
    have hm_eq : (2 * m) / 2 = m := by omega
    simp only [hm_eq]; exact h_init_bound
  -- Apply inductive bound
  have hlevels := sep_initial_levels_bound (2 * m) m₀ family.net ε₀ hε₀
    (family.isHalver) threshold ht_le_m₀ K w₀ hw₀_inj
    (ε₀ * ↑threshold) hD hD_half
  -- (K+1)*ε₀ = ε
  have hK_plus_1 : K + 1 = t := by
    show numSepLevels γ + 1 + 1 = sepTotalLayers γ; unfold sepTotalLayers; omega
  have hε_eq : ↑(K + 1) * ε₀ = (ε : ℝ) := by
    rw [hK_plus_1]
    show (↑t : ℝ) * ↑ε₀_Q = ↑ε
    have ht_ne : (↑t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hε₀_Q_def]
    push_cast
    rw [mul_div_cancel₀ _ ht_ne]
  -- Final calc chain
  calc (↑(univ.filter (fun pos : Fin (2 * m) ↦
        m₀ ≤ pos.val ∧ ((⟨(List.range K).reverse.flatMap fun k ↦
          sepLevelComparators (2 * m) family.net m₀ k⟩ :
          ComparatorNetwork (2 * m)).exec w₀ pos).val <
        threshold)).card : ℝ)
      ≤ ε₀ * ↑threshold + ↑K * ε₀ * ↑threshold := hlevels
    _ = ↑(K + 1) * ε₀ * ↑threshold := by push_cast; ring
    _ = ↑ε * ↑threshold := by rw [hε_eq]
    _ ≤ ↑ε * (γ' * ↑(2 * m)) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hε.le)
        rw [hthresh_def]
        exact_mod_cast Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
    _ = ↑ε * γ' * ↑(2 * m) := by ring


/-- Bijectivity preserves count of elements with value ≥ threshold. -/
lemma bijection_count_val_ge {n : ℕ}
    (w : Fin n → Fin n) (hw : Function.Injective w) (thresh : ℕ) :
    (univ.filter (fun pos : Fin n ↦ thresh ≤ (w pos).val)).card =
    (univ.filter (fun pos : Fin n ↦ thresh ≤ pos.val)).card := by
  have h1 := bijection_count_val_lt w hw thresh
  have h2 := Finset.card_filter_add_card_filter_not (s := univ)
    (fun pos : Fin n ↦ (w pos).val < thresh)
  have h3 := Finset.card_filter_add_card_filter_not (s := univ)
    (fun pos : Fin n ↦ pos.val < thresh)
  have h4 : ∀ (f : Fin n → ℕ), (univ.filter (fun pos ↦ thresh ≤ f pos)).card =
      (univ.filter (fun pos ↦ ¬ f pos < thresh)).card := by
    intro f; congr 1; ext i; simp only [mem_filter, mem_univ, true_and, not_lt]
  rw [h4 (fun pos ↦ (w pos).val), h4 (fun pos ↦ pos.val)]; omega


/-! **SepFinal direction helpers** -/

/-- Monotonicity for final displaced count: larger boundary → larger count. -/
lemma displaced_final_boundary_mono {n : ℕ} (w : Fin n → Fin n)
    (B₁ B₂ thresh : ℕ) (h : B₁ ≤ B₂) :
    (univ.filter (fun pos : Fin n ↦ pos.val < B₁ ∧ thresh ≤ (w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦ pos.val < B₂ ∧ thresh ≤ (w pos).val)).card :=
  card_le_card (fun pos hp ↦ by
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩)

/-- Final displaced count splits into far (< B₁) and near ([B₁, B₂)). -/
lemma displaced_final_split {n : ℕ} (w : Fin n → Fin n) (B₁ B₂ thresh : ℕ) :
    (univ.filter (fun pos : Fin n ↦ pos.val < B₂ ∧ thresh ≤ (w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦ pos.val < B₁ ∧ thresh ≤ (w pos).val)).card +
    (univ.filter (fun pos : Fin n ↦
      B₁ ≤ pos.val ∧ pos.val < B₂ ∧ thresh ≤ (w pos).val)).card := by
  calc _ ≤ ((univ.filter (fun pos : Fin n ↦ pos.val < B₁ ∧ thresh ≤ (w pos).val)) ∪
            (univ.filter (fun pos : Fin n ↦
              B₁ ≤ pos.val ∧ pos.val < B₂ ∧ thresh ≤ (w pos).val))).card := by
        apply card_le_card
        intro pos hp
        simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
        by_cases hlt : pos.val < B₁
        · left; exact ⟨hlt, hp.2⟩
        · right; push_neg at hlt; exact ⟨hlt, hp.1, hp.2⟩
    _ ≤ _ := card_union_le _ _

/-- Far positions (< offset) unchanged by suffix shiftEmbed. -/
lemma displaced_final_far_shiftEmbed_suffix {halfLen n : ℕ}
    (net : ComparatorNetwork (2 * halfLen))
    (h_fit : (n - 2 * halfLen) + 2 * halfLen ≤ n) (_h2hl : 2 * halfLen ≤ n)
    (v : Fin n → Fin n) (thresh : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < n - 2 * halfLen ∧
      thresh ≤ ((net.shiftEmbed n (n - 2 * halfLen) h_fit).exec v pos).val)).card =
    (univ.filter (fun pos : Fin n ↦
      pos.val < n - 2 * halfLen ∧ thresh ≤ (v pos).val)).card := by
  congr 1; ext pos
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨hlt, hge⟩
    exact ⟨hlt, by rwa [ComparatorNetwork.shiftEmbed_exec_outside
      net n (n - 2 * halfLen) h_fit v pos (Or.inl (by omega))] at hge⟩
  · intro ⟨hlt, hge⟩
    exact ⟨hlt, by rwa [ComparatorNetwork.shiftEmbed_exec_outside
      net n (n - 2 * halfLen) h_fit v pos (Or.inl (by omega))]⟩

/-- The suffix halver bounds large values in [n-2*halfLen, n-halfLen).
    Symmetric to `prefix_halver_near_bound`. -/
lemma suffix_halver_near_bound (halfLen n : ℕ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (halver : ComparatorNetwork (2 * halfLen))
    (hhalver : IsEpsilonHalver halver ε₀)
    (h_fit : (n - 2 * halfLen) + 2 * halfLen ≤ n)
    (v : Fin n → Fin n) (hv : Function.Injective v)
    (thresh : ℕ) (hthresh : n - thresh ≤ halfLen) :
    ((univ.filter (fun pos : Fin n ↦
      (n - 2 * halfLen) ≤ pos.val ∧ pos.val < (n - halfLen) ∧
      thresh ≤ ((halver.shiftEmbed n (n - 2 * halfLen) h_fit).exec v pos).val)).card : ℝ)
    ≤ ε₀ * ↑(n - thresh) := by
  set off := n - 2 * halfLen with hoff_def
  set exec_v := (halver.shiftEmbed n off h_fit).exec v
  by_cases hhl : halfLen = 0
  · have hempty : (univ.filter (fun pos : Fin n ↦
        off ≤ pos.val ∧ pos.val < n - halfLen ∧ thresh ≤ (exec_v pos).val)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; intro _ _ ⟨h1, h2, _⟩
      have : off = n := by show n - 2 * halfLen = n; omega
      omega
    have : ((univ.filter (fun pos : Fin n ↦
        off ≤ pos.val ∧ pos.val < n - halfLen ∧ thresh ≤ (exec_v pos).val)).card : ℝ) = 0 := by
      exact_mod_cast hempty
    rw [this]; exact mul_nonneg hε₀ (Nat.cast_nonneg _)
  have hhl_pos : 0 < halfLen := Nat.pos_of_ne_zero hhl
  -- Restrict v to [off, off+2*halfLen) = [off, n)
  set u : Fin (2 * halfLen) → Fin n :=
    fun j ↦ v ⟨off + j.val, by have := j.isLt; have := h_fit; omega⟩
  have hu : Function.Injective u := fun a b hab ↦ Fin.ext (by
    have := hv hab; simp only [Fin.mk.injEq] at this; omega)
  set a := (univ.filter (fun i : Fin (2 * halfLen) ↦ thresh ≤ (u i).val)).card
  have ha_le : a ≤ n - thresh := by
    convert injective_count_ge_le u hu (n - thresh) using 2
    ext i; simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro h <;> (have := (u i).isLt; omega)
  have ha_le_hl : a ≤ halfLen := le_trans ha_le hthresh
  have hbound := halver_injective_final_halved hhalver hε₀ u hu thresh ha_le_hl
  -- Bridge: shiftEmbed at offset off acts locally
  have h_exec_val : ∀ (pos : Fin n) (hpos : off ≤ pos.val) (hpos2 : pos.val < off + 2 * halfLen),
      (exec_v pos).val = (halver.exec u ⟨pos.val - off, by omega⟩).val := by
    intro pos hpos hpos2
    show ((halver.shiftEmbed n off h_fit).exec v pos).val = _
    have h := ComparatorNetwork.shiftEmbed_exec_inside halver n off h_fit v ⟨pos.val - off, by omega⟩
    simp only [hoff_def] at h
    show ((halver.shiftEmbed n off h_fit).exec v ⟨pos.val, pos.isLt⟩).val = _
    have hpos_eq : off + (pos.val - off) = pos.val := by omega
    rw [show (⟨pos.val, pos.isLt⟩ : Fin n) = ⟨off + (pos.val - off), by omega⟩ from by
      ext; show pos.val = off + (pos.val - off); omega]
    rw [h]
  -- Injection from near filter to halver filter
  have h_card_le : (univ.filter (fun pos : Fin n ↦
      off ≤ pos.val ∧ pos.val < n - halfLen ∧ thresh ≤ (exec_v pos).val)).card ≤
    (univ.filter (fun pos : Fin (2 * halfLen) ↦
      pos.val < halfLen ∧ thresh ≤ (halver.exec u pos).val)).card := by
    apply Finset.card_le_card_of_injOn (fun pos ↦ ⟨pos.val - off, by
      have := pos.isLt; omega⟩)
    · intro pos hp
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨by omega, ?_⟩
      rw [← h_exec_val pos hp.1 (by omega)]
      exact hp.2.2
    · intro a₁ ha₁ b₁ hb₁ hab
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at ha₁ hb₁
      ext; simp only [Fin.mk.injEq] at hab; omega
  calc ((univ.filter (fun pos : Fin n ↦ off ≤ pos.val ∧ pos.val < n - halfLen ∧
        thresh ≤ (exec_v pos).val)).card : ℝ)
      ≤ ↑(univ.filter (fun pos : Fin (2 * halfLen) ↦
          pos.val < halfLen ∧ thresh ≤ (halver.exec u pos).val)).card :=
        by exact_mod_cast h_card_le
    _ ≤ ε₀ * ↑a := hbound
    _ ≤ ε₀ * ↑(n - thresh) := mul_le_mul_of_nonneg_left (by exact_mod_cast ha_le) hε₀


/-! **Inductive Displaced Bound (SepFinal direction)** -/

/-- After processing j prefix-doubling levels, the final displaced
    count at boundary n - m₀ is bounded by D + j*ε₀*(n-thresh).
    Symmetric to `sep_initial_levels_bound`: suffix halvers control the
    near part, prefix halvers only help via `exec_displaced_final_le`. -/
lemma sep_final_levels_bound
    (n m₀ : ℕ)
    (halverNet : (m : ℕ) → ComparatorNetwork (2 * m))
    (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (hhalver : ∀ m, IsEpsilonHalver (halverNet m) ε₀)
    (thresh : ℕ) (ht : n - thresh ≤ m₀)
    (j : ℕ) (w : Fin n → Fin n) (hw : Function.Injective w)
    (D : ℝ) (hD : (↑(univ.filter (fun pos : Fin n ↦
      pos.val < n - 2 ^ j * m₀ ∧ thresh ≤ (w pos).val)).card : ℝ) ≤ D)
    (hD_half : (↑(univ.filter (fun pos : Fin n ↦
      pos.val < n / 2 ∧ thresh ≤ (w pos).val)).card : ℝ) ≤ ε₀ * ↑(n - thresh)) :
    (↑(univ.filter (fun pos : Fin n ↦
        pos.val < n - m₀ ∧ ((⟨((List.range j).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k)⟩ : ComparatorNetwork n).exec w pos).val ≥
        thresh)).card : ℝ) ≤ D + ↑j * ε₀ * ↑(n - thresh) := by
  induction j generalizing w D with
  | zero =>
    simp only [pow_zero, one_mul] at hD
    simp only [List.range_zero, List.reverse_nil, List.flatMap_nil,
      Nat.cast_zero, zero_mul, add_zero, ComparatorNetwork.exec, List.foldl_nil]
    exact hD
  | succ j ih =>
    have hdecomp : ((List.range (j + 1)).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k) =
      sepLevelComparators n halverNet m₀ j ++
      ((List.range j).reverse.flatMap fun k ↦ sepLevelComparators n halverNet m₀ k) := by
      rw [show List.range (j + 1) = List.range j ++ [j] from by rw [List.range_succ],
        List.reverse_append, List.flatMap_append]
      simp [List.flatMap_cons, List.flatMap_nil]
    rw [show (⟨((List.range (j+1)).reverse.flatMap fun k ↦
        sepLevelComparators n halverNet m₀ k)⟩ : ComparatorNetwork n) =
      ⟨sepLevelComparators n halverNet m₀ j ++
        ((List.range j).reverse.flatMap fun k ↦
          sepLevelComparators n halverNet m₀ k)⟩ from by
      exact congrArg _ hdecomp]
    rw [ComparatorNetwork.exec_append]
    set w₁ := (⟨sepLevelComparators n halverNet m₀ j⟩ : ComparatorNetwork n).exec w
    have hw₁ : Function.Injective w₁ := ComparatorNetwork.exec_injective _ hw
    have hD_half_w₁ : (↑(univ.filter (fun pos : Fin n ↦
        pos.val < n / 2 ∧ thresh ≤ (w₁ pos).val)).card : ℝ) ≤ ε₀ * ↑(n - thresh) :=
      calc _ ≤ ↑(univ.filter (fun pos : Fin n ↦
                pos.val < n / 2 ∧ thresh ≤ (w pos).val)).card := by
              exact_mod_cast exec_displaced_final_le
                ⟨sepLevelComparators n halverNet m₀ j⟩ w (n/2) thresh
           _ ≤ ε₀ * ↑(n - thresh) := hD_half
    suffices hstep : (↑(univ.filter (fun pos : Fin n ↦
        pos.val < n - 2 ^ j * m₀ ∧ thresh ≤ (w₁ pos).val)).card : ℝ) ≤
      D + ε₀ * ↑(n - thresh) by
      have := ih w₁ hw₁ (D + ε₀ * ↑(n - thresh)) hstep hD_half_w₁
      calc _ ≤ (D + ε₀ * ↑(n - thresh)) + ↑j * ε₀ * ↑(n - thresh) := this
        _ = D + ↑(j + 1) * ε₀ * ↑(n - thresh) := by push_cast; ring
    set halfLen := 2 ^ j * m₀ with hHL
    show (↑(univ.filter (fun pos : Fin n ↦ pos.val < n - halfLen ∧
      thresh ≤ ((⟨sepLevelComparators n halverNet m₀ j⟩ : ComparatorNetwork n).exec w pos).val
      )).card : ℝ) ≤ D + ε₀ * ↑(n - thresh)
    by_cases h_suffix_fit : (n - 2 * halfLen) + 2 * halfLen ≤ n
    · -- Suffix halver fits: split into far + near directly
      unfold sepLevelComparators
      -- Decompose: exec (prefix ++ suffix) w = exec suffix (exec prefix w)
      rw [show ((if h : 0 + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n 0 h).comparators else []) ++
          (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
          else [])) =
        (if h : 0 + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n 0 h).comparators else []) ++
          (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
          else []) from rfl,
        ComparatorNetwork.exec_append, dif_pos h_suffix_fit]
      set w_prefix := (⟨if h : 0 + 2 * halfLen ≤ n then
        ((halverNet halfLen).shiftEmbed n 0 h).comparators else []⟩ :
        ComparatorNetwork n).exec w
      have hw_prefix_inj : Function.Injective w_prefix :=
        ComparatorNetwork.exec_injective _ hw
      have h2hl_le : 2 * halfLen ≤ n := by omega
      -- Split displaced_final at n-halfLen into far (< n-2*halfLen) + near
      have hsplit := displaced_final_split
        (((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h_suffix_fit).exec w_prefix)
        (n - 2 * halfLen) (n - halfLen) thresh
      -- Far: suffix doesn't change positions < n-2*halfLen, then prefix helps
      have hfar : (↑(univ.filter (fun pos : Fin n ↦ pos.val < n - 2 * halfLen ∧ thresh ≤
          (((halverNet halfLen).shiftEmbed n (n - 2 * halfLen)
            h_suffix_fit).exec w_prefix pos).val)).card : ℝ) ≤ D := by
        rw [displaced_final_far_shiftEmbed_suffix _ h_suffix_fit h2hl_le _ _]
        have h2hl_eq : 2 * halfLen = 2 ^ (j + 1) * m₀ := by
          show 2 * (2 ^ j * m₀) = 2 ^ (j + 1) * m₀; rw [pow_succ]; ring
        calc _ ≤ ↑(univ.filter (fun pos : Fin n ↦ pos.val < n - 2 * halfLen ∧
                thresh ≤ (w pos).val)).card := by
              exact_mod_cast exec_displaced_final_le _ w (n - 2 * halfLen) thresh
          _ ≤ D := by
            suffices h : (univ.filter (fun pos : Fin n ↦ pos.val < n - 2 * halfLen ∧
                thresh ≤ (w pos).val)) =
              (univ.filter (fun pos : Fin n ↦ pos.val < n - 2 ^ (j + 1) * m₀ ∧
                thresh ≤ (w pos).val)) by rw [h]; exact hD
            congr 1; ext pos; exact and_congr_left' (by rw [h2hl_eq])
      -- Near: suffix halver bounds large values in [n-2*halfLen, n-halfLen)
      have hm₀_le_hl : m₀ ≤ halfLen :=
        Nat.le_mul_of_pos_left m₀ (pow_pos (by norm_num : 0 < 2) j)
      have hnear := suffix_halver_near_bound halfLen n ε₀ hε₀
        (halverNet halfLen) (hhalver halfLen) h_suffix_fit w_prefix hw_prefix_inj
        thresh (le_trans ht hm₀_le_hl)
      -- Combine far + near
      calc _ ≤ ↑((univ.filter (fun pos : Fin n ↦ pos.val < n - 2 * halfLen ∧ thresh ≤
                (((halverNet halfLen).shiftEmbed n (n - 2 * halfLen)
                  h_suffix_fit).exec w_prefix pos).val)).card +
              (univ.filter (fun pos : Fin n ↦ (n - 2 * halfLen) ≤ pos.val ∧
                pos.val < n - halfLen ∧ thresh ≤
                (((halverNet halfLen).shiftEmbed n (n - 2 * halfLen)
                  h_suffix_fit).exec w_prefix pos).val)).card) := by
            exact_mod_cast hsplit
        _ ≤ D + ε₀ * ↑(n - thresh) := by push_cast; linarith
    · -- No-op case
      push_neg at h_suffix_fit
      have hhl_ge : halfLen ≥ n / 2 := by omega
      calc (↑(univ.filter (fun pos : Fin n ↦ pos.val < n - halfLen ∧
              thresh ≤ ((⟨sepLevelComparators n halverNet m₀ j⟩ :
                ComparatorNetwork n).exec w pos).val)).card : ℝ)
          ≤ ↑(univ.filter (fun pos : Fin n ↦ pos.val < n - halfLen ∧
              thresh ≤ (w pos).val)).card := by
            exact_mod_cast exec_displaced_final_le
              ⟨sepLevelComparators n halverNet m₀ j⟩ w (n - halfLen) thresh
        _ ≤ ↑(univ.filter (fun pos : Fin n ↦ pos.val < n / 2 ∧
              thresh ≤ (w pos).val)).card := by
            exact_mod_cast displaced_final_boundary_mono w (n - halfLen) (n / 2) thresh (by omega)
        _ ≤ ε₀ * ↑(n - thresh) := hD_half
        _ ≤ D + ε₀ * ↑(n - thresh) := by
            linarith [le_trans (Nat.cast_nonneg (univ.filter (fun pos : Fin n ↦
              pos.val < n - 2 ^ (j + 1) * m₀ ∧ thresh ≤ (w pos).val)).card) hD]


/-! **SepFinal direction** -/

/-- The prefix-doubling separator satisfies `SepFinal`. -/
theorem separatorNet_sepFinal (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε)
    (hγ_le : γ ≤ 1 / 2) (m : ℕ) (v : Equiv.Perm (Fin (2 * m))) :
    SepFinal ((separatorNet γ ε hγ hε m).exec v) ↑γ ↑ε := by
  -- SepFinal = SepInitial for order dual
  show SepInitial (α := (Fin (2 * m))ᵒᵈ) _ _ _
  -- Trivial case
  by_cases hfloor : ⌊(γ : ℝ) * ↑(2 * m)⌋₊ = 0
  · exact sepFinal_trivial _ ↑γ ↑ε (by exact_mod_cast hε.le) (by exact_mod_cast hγ.le) hfloor
  have hfloor_pos : 0 < ⌊(γ : ℚ) * ↑(2 * m)⌋₊ := by
    rw [(floor_rat_real_mul_nat γ (2 * m) hγ.le).symm]; exact Nat.pos_of_ne_zero hfloor
  -- Setup (same as SepInitial)
  set t := sepTotalLayers γ with ht_def
  set ε₀_Q := ε / ↑t with hε₀_Q_def
  have hε₀_Q_pos : (0 : ℚ) < ε₀_Q := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  set family := halvers ε₀_Q hε₀_Q_pos
  set m₀ := sepBaseChunk γ (2 * m) with hm₀_def
  set K := numSepLevels γ + 1 with hK_def
  have hm₀_eq : m₀ = ⌊(γ : ℚ) * ↑(2 * m)⌋₊ := sepBaseChunk_eq_floor γ (2 * m) hfloor_pos
  have hm₀_pos : 0 < m₀ := by omega
  set ε₀ : ℝ := ↑ε₀_Q with hε₀_def
  have hε₀ : (0 : ℝ) ≤ ε₀ := by show (0 : ℝ) ≤ ↑ε₀_Q; exact_mod_cast hε₀_Q_pos.le
  have hsep_eq : (separatorNet γ ε hγ hε m).comparators =
      (family.net m).comparators ++
      ((List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k) := by
    unfold separatorNet; rfl
  set w₀ := (family.net m).exec (v : Fin (2 * m) → Fin (2 * m))
  have hw₀_inj : Function.Injective w₀ :=
    ComparatorNetwork.exec_injective _ v.injective
  have hresult_eq : (separatorNet γ ε hγ hε m).exec (v : Fin (2 * m) → Fin (2 * m)) =
      (⟨(List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k⟩ :
        ComparatorNetwork (2 * m)).exec w₀ := by
    show (⟨(separatorNet γ ε hγ hε m).comparators⟩ : ComparatorNetwork (2 * m)).exec v = _
    rw [hsep_eq, ComparatorNetwork.exec_append]
  -- Open SepInitial (order dual), simplify
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od, rank_fin_od_fin]
  simp_rw [hresult_eq, floor_rat_real_mul_nat γ (2 * m) hγ.le, ← hm₀_eq]
  -- Bridge from OD conditions to val conditions via suffices
  set threshold := ⌊γ' * ↑(2 * m)⌋₊ with hthresh_def
  set thresh := 2 * m - threshold with hthresh_final_def
  -- suffices: concrete val-based bound
  suffices h : ((univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < 2 * m - m₀ ∧ thresh ≤ ((⟨(List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k⟩ :
        ComparatorNetwork (2 * m)).exec w₀ pos).val)).card : ℝ) ≤
    ↑ε * γ' * ↑(2 * m) by
    calc ((univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
          m₀ ≤ 2 * m - 1 - pos.val ∧
          2 * m - 1 - ((⟨(List.range K).reverse.flatMap fun k ↦
            sepLevelComparators (2 * m) family.net m₀ k⟩ :
            ComparatorNetwork (2 * m)).exec w₀ pos).val <
          threshold)).card : ℝ)
        = ((univ.filter (fun pos : Fin (2 * m) ↦
            pos.val < 2 * m - m₀ ∧ thresh ≤ ((⟨(List.range K).reverse.flatMap fun k ↦
              sepLevelComparators (2 * m) family.net m₀ k⟩ :
              ComparatorNetwork (2 * m)).exec w₀ pos).val)).card : ℝ) := by
          congr 1
          apply Finset.card_nbij'
            (fun a : (Fin (2 * m))ᵒᵈ ↦ (a : Fin (2 * m)))
            (fun b : Fin (2 * m) ↦ (b : (Fin (2 * m))ᵒᵈ))
          · intro a ha
            simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at ha
            have := (a : Fin (2 * m)).isLt
            have := ((⟨(List.range K).reverse.flatMap fun k ↦
              sepLevelComparators (2 * m) family.net m₀ k⟩ :
              ComparatorNetwork (2 * m)).exec w₀ (a : Fin (2 * m))).isLt
            exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by dsimp only; omega, by dsimp only; omega⟩)
          · intro b hb
            have hbm := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
            have := b.isLt
            have := ((⟨(List.range K).reverse.flatMap fun k ↦
              sepLevelComparators (2 * m) family.net m₀ k⟩ :
              ComparatorNetwork (2 * m)).exec w₀ b).isLt
            refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩)
            · show m₀ ≤ 2 * m - 1 - b.val; omega
            · show 2 * m - 1 - ((⟨(List.range K).reverse.flatMap fun k ↦
                sepLevelComparators (2 * m) family.net m₀ k⟩ :
                ComparatorNetwork (2 * m)).exec w₀ b).val < threshold; omega
          all_goals intro _ _; rfl
      _ ≤ _ := h
  -- threshold ≤ m₀
  have ht_le_m₀ : threshold ≤ m₀ := by
    rw [hthresh_def, hm₀_eq, ← floor_rat_real_mul_nat γ (2 * m) hγ.le]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hγ'_le (Nat.cast_nonneg _))
  have ht_le_m : threshold ≤ m := by
    calc threshold ≤ ⌊(1 / 2 : ℝ) * ↑(2 * m)⌋₊ := by
          rw [hthresh_def]; apply Nat.floor_le_floor
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          calc γ' ≤ ↑γ := hγ'_le
            _ ≤ ↑(1 / 2 : ℚ) := by exact_mod_cast hγ_le
            _ = 1 / 2 := by push_cast; ring
      _ = m := by
          rw [show (1 / 2 : ℝ) * ↑(2 * m) = ↑m from by push_cast; ring]
          exact Nat.floor_natCast m
  have hthresh_le_n : thresh ≤ 2 * m := by omega
  have h_nt : 2 * m - thresh = threshold := by omega
  -- Initial halver bound (final direction)
  have h_perm_count_ge : (univ.filter (fun i : Fin (2 * m) ↦
      thresh ≤ (v i : Fin (2 * m)).val)).card = threshold := by
    rw [bijection_count_val_ge v v.injective, card_filter_val_ge (2 * m) thresh hthresh_le_n, h_nt]
  have h_init_bound : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ thresh ≤ (w₀ pos).val)).card : ℝ) ≤ ε₀ * ↑threshold := by
    have hmain := halver_injective_final_halved (family.isHalver m) hε₀
      (v : Fin (2 * m) → Fin (2 * m)) v.injective thresh
    have ha_le : (univ.filter (fun i : Fin (2 * m) ↦
        thresh ≤ (v i : Fin (2 * m)).val)).card ≤ m := by
      rw [h_perm_count_ge]; exact ht_le_m
    have hh := hmain ha_le
    simp only [h_perm_count_ge] at hh
    exact hh
  -- Coverage
  have hcov : m ≤ 2 ^ K * m₀ := coverage_nat γ m hγ
  -- displaced_final(2m - 2^K*m₀, w₀) ≤ ε₀*threshold
  have h_cov_le : 2 * m - 2 ^ K * m₀ ≤ m := by omega
  have hD : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < 2 * m - 2 ^ K * m₀ ∧ thresh ≤ (w₀ pos).val)).card : ℝ) ≤
      ε₀ * ↑threshold :=
    calc _ ≤ ↑(univ.filter (fun pos : Fin (2 * m) ↦
            pos.val < m ∧ thresh ≤ (w₀ pos).val)).card := by
          exact_mod_cast displaced_final_boundary_mono w₀ (2 * m - 2 ^ K * m₀) m
            thresh h_cov_le
       _ ≤ ε₀ * ↑threshold := h_init_bound
  have hD_half : (↑(univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < (2 * m) / 2 ∧ thresh ≤ (w₀ pos).val)).card : ℝ) ≤
      ε₀ * ↑threshold := by
    have hm_eq : (2 * m) / 2 = m := by omega
    simp only [hm_eq]; exact h_init_bound
  -- Apply inductive bound
  have hlevels := sep_final_levels_bound (2 * m) m₀ family.net ε₀ hε₀
    (family.isHalver) thresh (by have := ht_le_m; omega) K w₀ hw₀_inj
    (ε₀ * ↑threshold) (by convert hD using 3)
    (by convert hD_half using 3)
  rw [show (2 * m - thresh) = threshold from h_nt] at hlevels
  -- (K+1)*ε₀ = ε
  have hK_plus_1 : K + 1 = t := by
    show numSepLevels γ + 1 + 1 = sepTotalLayers γ; unfold sepTotalLayers; omega
  have hε_eq : ↑(K + 1) * ε₀ = (ε : ℝ) := by
    rw [hK_plus_1]; show (↑t : ℝ) * ↑ε₀_Q = ↑ε
    have ht_ne : (↑t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hε₀_Q_def]; push_cast; rw [mul_div_cancel₀ _ ht_ne]
  -- Final calc chain
  calc (↑(univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < 2 * m - m₀ ∧ thresh ≤ ((⟨(List.range K).reverse.flatMap fun k ↦
          sepLevelComparators (2 * m) family.net m₀ k⟩ :
          ComparatorNetwork (2 * m)).exec w₀ pos).val)).card : ℝ)
      ≤ ε₀ * ↑threshold + ↑K * ε₀ * ↑threshold := hlevels
    _ = ↑(K + 1) * ε₀ * ↑threshold := by push_cast; ring
    _ = ↑ε * ↑threshold := by rw [hε_eq]
    _ ≤ ↑ε * (γ' * ↑(2 * m)) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hε.le)
        rw [hthresh_def]
        exact_mod_cast Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
    _ = ↑ε * γ' * ↑(2 * m) := by ring


/-! **Separator Property** -/

theorem separatorNet_isSeparator (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε)
    (hγ_le : γ ≤ 1 / 2) (m : ℕ) :
    IsSeparator (separatorNet γ ε hγ hε m) ↑γ ↑ε := by
  intro v
  exact ⟨separatorNet_sepInitial γ ε hγ hε hγ_le m v,
         separatorNet_sepFinal γ ε hγ hε hγ_le m v⟩

/-- The prefix-doubling separator is an ε-halver: the initial halver layer
    gives `IsEpsilonHalver ε₀`, appending prefix/suffix layers preserves it
    (`IsEpsilonHalver_append`), and `ε₀ ≤ ε` gives `IsEpsilonHalver ε`. -/
theorem separatorNet_isHalver (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε)
    (m : ℕ) : IsEpsilonHalver (separatorNet γ ε hγ hε m) ↑ε := by
  -- Setup: decompose separatorNet into halver ++ remaining layers
  set t := sepTotalLayers γ
  set ε₀_Q := ε / ↑t with hε₀_Q_def
  have hε₀_Q_pos : (0 : ℚ) < ε₀_Q := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  set family := halvers ε₀_Q hε₀_Q_pos
  set m₀ := sepBaseChunk γ (2 * m)
  set K := numSepLevels γ + 1
  -- ε₀ ≤ ε
  have hε₀_le : (ε₀_Q : ℝ) ≤ (ε : ℝ) := by
    exact_mod_cast div_le_self hε.le (by exact_mod_cast sepTotalLayers_pos γ : (1 : ℚ) ≤ ↑t)
  -- separatorNet = family.net m ++ remaining layers
  have hsep_eq : (separatorNet γ ε hγ hε m).comparators =
      (family.net m).comparators ++
      ((List.range K).reverse.flatMap fun k ↦
        sepLevelComparators (2 * m) family.net m₀ k) := by
    unfold separatorNet; rfl
  -- The initial halver is an ε₀-halver
  have h_init : IsEpsilonHalver (family.net m) ↑ε₀_Q := family.isHalver m
  -- Appending preserves the halver property
  let remaining : ComparatorNetwork (2 * m) :=
    ⟨(List.range K).reverse.flatMap fun k ↦
      sepLevelComparators (2 * m) family.net m₀ k⟩
  have h_append : IsEpsilonHalver ⟨(family.net m).comparators ++ remaining.comparators⟩ ↑ε₀_Q :=
    IsEpsilonHalver_append h_init remaining
  -- separatorNet = halver ++ remaining
  have h_eq : separatorNet γ ε hγ hε m = ⟨(family.net m).comparators ++ remaining.comparators⟩ :=
    ComparatorNetwork.ext hsep_eq
  rw [h_eq]
  exact h_append.mono hε₀_le

def separators (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε)
    (hγ_le : γ ≤ 1 / 2 := by norm_num) : SeparatorFamily γ ε where
  depth := separatorDepth γ ε hγ hε
  net m := separatorNet γ ε hγ hε m
  isSeparator m := separatorNet_isSeparator γ ε hγ hε hγ_le m
  isHalver m := separatorNet_isHalver γ ε hγ hε m
  depth_le m := separatorNet_depth_le γ ε hγ hε m

end


