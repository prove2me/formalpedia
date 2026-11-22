-- Prove2me | Definitions.Def_GirvingAKS_Separator_General
-- name    : GirvingAKS_Separator_General
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:47:50.543208+00:00
-- url     : https://prove2.me/theorems/84396173-3df9-4938-88dd-a25a7e5a552e
-- title:
--   AKS sorting networks (Seiferas port) — General Separator Family via Prefix-Doubling
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Separator/General.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Builds a `SeparatorFamily γ ε` for arbitrary `γ` and `ε` using the Seiferas (2009) Section 6, Lemma 2 prefix-doubling construction.
--
--   Given ε₀-halvers at all even sizes:
--
--   1. **Initial halving:** Apply halver to all `n = 2m` wires
--   2. **Prefix/suffix refinement:** For each level `k`, apply halvers to
--
--   prefixes of length `2^(k+1)·m₀` and suffixes of the same length, where `m₀ = max(1, ⌊γ·n⌋₊)`.
--
--   All prefix/suffix lengths are multiples of `2m₀` (always even), so halvers apply at any even wire count without divisibility constraints.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Separator/General.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Separator_FromHalver
import Definitions.Def_GirvingAKS_Halver_General
import Definitions.Def_GirvingAKS_Sort_Displaced

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Separator/General.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # General Separator Family via Prefix-Doubling

  Builds a `SeparatorFamily γ ε` for arbitrary `γ` and `ε` using the
  Seiferas (2009) Section 6, Lemma 2 prefix-doubling construction.

  Given ε₀-halvers at all even sizes:
  1. **Initial halving:** Apply halver to all `n = 2m` wires
  2. **Prefix/suffix refinement:** For each level `k`, apply halvers to
     prefixes of length `2^(k+1)·m₀` and suffixes of the same length,
     where `m₀ = max(1, ⌊γ·n⌋₊)`.

  All prefix/suffix lengths are multiples of `2m₀` (always even), so
  halvers apply at any even wire count without divisibility constraints.

-/


section


/-! **Level Counting** -/

/-- Number of prefix-doubling levels needed for target fraction `γ`.
    Equals `⌈log₂(⌈1/(2γ)⌉)⌉` when `γ > 0`, giving `2^result ≥ ⌈1/(2γ)⌉`.
    Returns 0 for `γ ≤ 0` or `γ ≥ 1/2`. -/
def numSepLevels (γ : ℚ) : ℕ :=
  if 0 < γ then Nat.clog 2 ⌈(1 : ℚ) / (2 * γ)⌉₊
  else 0

/-- Total halver layers: initial halving + `numSepLevels + 1` prefix levels. -/
def sepTotalLayers (γ : ℚ) : ℕ := numSepLevels γ + 2

/-- `sepTotalLayers γ ≥ 1` for all `γ`. -/
lemma sepTotalLayers_pos (γ : ℚ) : 0 < sepTotalLayers γ := by
  unfold sepTotalLayers; omega

/-- Coverage: `2^(numSepLevels γ + 1) * γ ≥ 1` for `0 < γ`.
    Equivalently: `2^K * m₀ ≥ m` where `K = numSepLevels γ + 1`,
    `m₀ ≥ γ·n`, and `n = 2m`. -/
lemma numSepLevels_coverage (γ : ℚ) (hγ : 0 < γ) :
    (2 : ℚ) ^ (numSepLevels γ + 1) * γ ≥ 1 := by
  unfold numSepLevels; rw [if_pos hγ]
  set c := ⌈(1 : ℚ) / (2 * γ)⌉₊
  rw [pow_succ]
  suffices h : (2 : ℚ) ^ Nat.clog 2 c * (2 * γ) ≥ 1 by linarith
  have hclog : c ≤ 2 ^ Nat.clog 2 c := Nat.le_pow_clog (by norm_num) c
  have hc : (1 : ℚ) / (2 * γ) ≤ ↑c := Nat.le_ceil _
  have h2γ : (0 : ℚ) < 2 * γ := by linarith
  calc (2 : ℚ) ^ Nat.clog 2 c * (2 * γ)
      ≥ ↑c * (2 * γ) := by
        apply mul_le_mul_of_nonneg_right _ h2γ.le
        exact_mod_cast hclog
    _ ≥ (1 / (2 * γ)) * (2 * γ) := mul_le_mul_of_nonneg_right hc h2γ.le
    _ = 1 := by field_simp


/-! **Prefix-Doubling Separator Construction** -/

/-- Base chunk size for prefix-doubling: `m₀ = max(1, ⌊γ·n⌋₊)`. -/
def sepBaseChunk (γ : ℚ) (n : ℕ) : ℕ := max 1 ⌊γ * ↑n⌋₊

/-- Build the prefix/suffix halver layers for one level `k`.
    Applies halver to prefix `[0, 2^(k+1)·m₀)` and suffix
    `[n − 2^(k+1)·m₀, n)`, each of length `2·halfLen` where
    `halfLen = 2^k · m₀`. -/
def sepLevelComparators (n : ℕ)
    (halverNet : (m : ℕ) → ComparatorNetwork (2 * m))
    (m₀ : ℕ) (k : ℕ) : List (Comparator n) :=
  let halfLen := 2 ^ k * m₀
  -- Prefix halver: [0, 2 * halfLen)
  (if h : 0 + 2 * halfLen ≤ n then
    ((halverNet halfLen).shiftEmbed n 0 h).comparators
  else []) ++
  -- Suffix halver: [n - 2 * halfLen, n)
  (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
    ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
  else [])

/-- The prefix-doubling separator network for `2 * m` wires.

    Step 1: Apply ε₀-halver to all `2m` wires (split at position `m`).
    Step 2: For each level `k = K-1, ..., 0`, apply halvers to prefix
    and suffix of length `2^(k+1) · m₀`.

    Uses `K = numSepLevels(γ) + 1` prefix levels.
    The halver error is `ε₀ = ε / sepTotalLayers(γ)`, so total error
    ≤ sepTotalLayers(γ) · ε₀ = ε. -/
def separatorNet (γ ε : ℚ) (_hγ : 0 < γ) (hε : 0 < ε)
    (m : ℕ) : ComparatorNetwork (2 * m) :=
  let t := sepTotalLayers γ
  let ε₀ := ε / ↑t
  have hε₀ : (0 : ℚ) < ε₀ := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  let family := halvers ε₀ hε₀
  let n := 2 * m
  let m₀ := sepBaseChunk γ n
  { comparators :=
      -- Step 1: halve all n wires
      (family.net m).comparators ++
      -- Step 2: prefix/suffix at doubling sizes (largest first)
      ((List.range (numSepLevels γ + 1)).reverse.flatMap fun k ↦
        sepLevelComparators n family.net m₀ k) }

/-- Depth bound for the prefix-doubling separator construction.
    At each level, prefix and suffix halvers may overlap (when
    `4 · halfLen > n`), giving worst-case 2 sequential depths per level.
    Total depth ≤ `(2 · (numSepLevels(γ) + 1) + 1) · halverDepth(ε₀)`. -/
def separatorDepth (γ ε : ℚ) (_hγ : 0 < γ) (hε : 0 < ε) : ℕ :=
  let t := sepTotalLayers γ
  let ε₀ := ε / ↑t
  have hε₀ : (0 : ℚ) < ε₀ := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  (2 * (numSepLevels γ + 1) + 1) * (halvers ε₀ hε₀).depth


/-! **Separator Property** -/

/-- When `⌊γn⌋₊ = 0`, `SepInitial` holds trivially: the filter set is empty
    because `⌊γ'n⌋₊ = 0` for all `γ' ≤ γ`. -/
lemma sepInitial_trivial {n : ℕ} (w : Fin n → Fin n) (γ ε : ℝ)
    (hε : 0 ≤ ε) (_hγ : 0 ≤ γ) (hfloor : ⌊γ * ↑n⌋₊ = 0) :
    SepInitial w γ ε := by
  intro γ' hγ' hγ'_le
  have hfloor' : ⌊γ' * ↑n⌋₊ = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc ⌊γ' * ↑n⌋₊ ≤ ⌊γ * ↑n⌋₊ :=
          Nat.floor_le_floor (mul_le_mul_of_nonneg_right hγ'_le (Nat.cast_nonneg _))
      _ = 0 := hfloor
  have hempty : (Finset.univ.filter (fun pos : Fin n ↦
      ⌊γ * ↑(Fintype.card (Fin n))⌋₊ ≤ rank pos ∧
        rank (w pos) < ⌊γ' * ↑(Fintype.card (Fin n))⌋₊)).card = 0 := by
    rw [show Fintype.card (Fin n) = n from Fintype.card_fin n, hfloor']
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro _ _ ⟨_, h⟩; omega
  show (↑(Finset.univ.filter _).card : ℝ) ≤ _
  rw [hempty]; push_cast
  exact mul_nonneg (mul_nonneg hε hγ') (Nat.cast_nonneg _)

/-- When `⌊γn⌋₊ = 0`, `SepFinal` holds trivially (dual). -/
lemma sepFinal_trivial {n : ℕ} (w : Fin n → Fin n) (γ ε : ℝ)
    (hε : 0 ≤ ε) (_hγ : 0 ≤ γ) (hfloor : ⌊γ * ↑n⌋₊ = 0) :
    SepFinal w γ ε := by
  show SepInitial (α := (Fin n)ᵒᵈ) w γ ε
  intro γ' hγ' hγ'_le
  have hfloor' : ⌊γ' * ↑n⌋₊ = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc ⌊γ' * ↑n⌋₊ ≤ ⌊γ * ↑n⌋₊ :=
          Nat.floor_le_floor (mul_le_mul_of_nonneg_right hγ'_le (Nat.cast_nonneg _))
      _ = 0 := hfloor
  have hempty : (Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
      ⌊γ * ↑(Fintype.card (Fin n)ᵒᵈ)⌋₊ ≤ @rank _ (OrderDual.fintype _)
        (OrderDual.instLinearOrder _) pos ∧
        @rank _ (OrderDual.fintype _) (OrderDual.instLinearOrder _) (w pos) <
          ⌊γ' * ↑(Fintype.card (Fin n)ᵒᵈ)⌋₊)).card = 0 := by
    simp only [Fintype.card_orderDual, Fintype.card_fin, hfloor']
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro _ _ ⟨_, h⟩; omega
  calc (↑(Finset.univ.filter _).card : ℝ) = ↑(0 : ℕ) := by exact_mod_cast hempty
    _ ≤ ε * γ' * ↑(Fintype.card (Fin n)ᵒᵈ) := by
        push_cast; exact mul_nonneg (mul_nonneg hε hγ') (Nat.cast_nonneg _)

/-! **Depth helpers** -/

/-- Depth of flatMap ≤ sum of per-element depths. -/
lemma depth_flatMap_le_sum {n : ℕ} {ι : Type*} (l : List ι)
    (f : ι → List (Comparator n)) :
    (⟨l.flatMap f⟩ : ComparatorNetwork n).depth ≤
    (l.map (fun x ↦ (⟨f x⟩ : ComparatorNetwork n).depth)).sum := by
  induction l with
  | nil => simp [List.flatMap_nil, ComparatorNetwork.depth]
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    calc (⟨f x ++ xs.flatMap f⟩ : ComparatorNetwork n).depth
        ≤ (⟨f x⟩ : ComparatorNetwork n).depth +
          (⟨xs.flatMap f⟩ : ComparatorNetwork n).depth :=
          depth_append ⟨f x⟩ ⟨xs.flatMap f⟩
      _ ≤ _ + _ := Nat.add_le_add_left ih _

/-- Depth of each `sepLevelComparators` ≤ 2 * halver depth.
    Prefix and suffix halvers are concatenated; each is a `shiftEmbed`
    with depth ≤ the original halver's depth. -/
lemma depth_sepLevelComparators_le {n : ℕ}
    {halverNet : (m : ℕ) → ComparatorNetwork (2 * m)} {d : ℕ}
    (hd : ∀ m, (halverNet m).depth ≤ d) (m₀ k : ℕ) :
    (⟨sepLevelComparators n halverNet m₀ k⟩ : ComparatorNetwork n).depth ≤ 2 * d := by
  unfold sepLevelComparators
  set halfLen := 2 ^ k * m₀
  -- depth of prefix ++ suffix ≤ depth prefix + depth suffix
  calc (⟨(if h : 0 + 2 * halfLen ≤ n then
        ((halverNet halfLen).shiftEmbed n 0 h).comparators else []) ++
      (if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
        ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
      else [])⟩ : ComparatorNetwork n).depth
      ≤ (⟨if h : 0 + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n 0 h).comparators
          else []⟩ : ComparatorNetwork n).depth +
        (⟨if h : (n - 2 * halfLen) + 2 * halfLen ≤ n then
            ((halverNet halfLen).shiftEmbed n (n - 2 * halfLen) h).comparators
          else []⟩ : ComparatorNetwork n).depth := by
        exact depth_append _ _
    _ ≤ d + d := by
        apply Nat.add_le_add
        · by_cases hp : 0 + 2 * halfLen ≤ n
          · rw [dif_pos hp]
            exact (depth_shiftEmbed_le (halverNet halfLen) n 0 hp).trans (hd _)
          · rw [dif_neg hp]; simp [ComparatorNetwork.depth]
        · by_cases hs : (n - 2 * halfLen) + 2 * halfLen ≤ n
          · rw [dif_pos hs]
            exact (depth_shiftEmbed_le (halverNet halfLen) n _ hs).trans (hd _)
          · rw [dif_neg hs]; simp [ComparatorNetwork.depth]
    _ = 2 * d := by omega


/-- Depth bound for `separatorNet`. -/
theorem separatorNet_depth_le (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) (m : ℕ) :
    (separatorNet γ ε hγ hε m).depth ≤ separatorDepth γ ε hγ hε := by
  unfold separatorNet separatorDepth
  set t := sepTotalLayers γ
  set ε₀ := ε / ↑t
  set hε₀ : (0 : ℚ) < ε₀ := div_pos hε (Nat.cast_pos.mpr (sepTotalLayers_pos γ))
  set family := halvers ε₀ hε₀
  set n := 2 * m
  set m₀ := sepBaseChunk γ n
  set K := numSepLevels γ + 1
  show (⟨(family.net m).comparators ++
    ((List.range K).reverse.flatMap fun k ↦
      sepLevelComparators n family.net m₀ k)⟩ : ComparatorNetwork (2 * m)).depth ≤
    (2 * K + 1) * family.depth
  calc (⟨(family.net m).comparators ++ _⟩ : ComparatorNetwork (2 * m)).depth
      ≤ (family.net m).depth +
        (⟨(List.range K).reverse.flatMap fun k ↦
          sepLevelComparators n family.net m₀ k⟩ :
          ComparatorNetwork (2 * m)).depth := depth_append _ _
    _ ≤ family.depth +
        (⟨(List.range K).reverse.flatMap fun k ↦
          sepLevelComparators n family.net m₀ k⟩ :
          ComparatorNetwork (2 * m)).depth :=
        Nat.add_le_add_right (family.depth_le m) _
    _ ≤ family.depth +
        ((List.range K).reverse.map (fun k ↦
          (⟨sepLevelComparators n family.net m₀ k⟩ :
            ComparatorNetwork (2 * m)).depth)).sum :=
        Nat.add_le_add_left (depth_flatMap_le_sum _ _) _
    _ = family.depth +
        ((List.range K).map (fun k ↦
          (⟨sepLevelComparators n family.net m₀ k⟩ :
            ComparatorNetwork (2 * m)).depth)).sum := by
        rw [List.map_reverse, List.sum_reverse]
    _ ≤ family.depth + K * (2 * family.depth) := by
        apply Nat.add_le_add_left
        have hbound := List.sum_le_card_nsmul
          ((List.range K).map (fun k ↦
            (⟨sepLevelComparators n family.net m₀ k⟩ :
              ComparatorNetwork (2 * m)).depth))
          (2 * family.depth)
          (by intro d hd
              rw [List.mem_map] at hd
              obtain ⟨k, _, rfl⟩ := hd
              exact depth_sepLevelComparators_le family.depth_le m₀ k)
        simp only [List.length_map, List.length_range] at hbound
        exact_mod_cast hbound
    _ = (2 * K + 1) * family.depth := by ring


/-! **Antitonicity** -/

/-- `numSepLevels` is antitone: larger γ → smaller `⌈1/(2γ)⌉₊` → fewer prefix-doubling levels. -/
theorem numSepLevels_antitone {γ₁ γ₂ : ℚ} (hγ₁ : 0 < γ₁) (h : γ₁ ≤ γ₂) :
    numSepLevels γ₂ ≤ numSepLevels γ₁ := by
  have hγ₂ : 0 < γ₂ := lt_of_lt_of_le hγ₁ h
  unfold numSepLevels
  rw [if_pos hγ₁, if_pos hγ₂]
  apply Nat.clog_mono_right
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_left (by norm_num : (0:ℚ) < 1).le
    (mul_pos two_pos hγ₁)
    (mul_le_mul_of_nonneg_left h two_pos.le)

/-- `separatorDepth` is antitone in γ: larger γ → fewer levels and larger per-layer ε₀ → less depth.
    Uses `numSepLevels_antitone` (both the level-count factor and the total-layers denominator)
    and `halverDepth_antitone` (larger ε₀ → fewer squarings → less depth). -/
theorem separatorDepth_antitone {γ₁ γ₂ : ℚ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (h : γ₁ ≤ γ₂)
    {ε : ℚ} (hε : 0 < ε) :
    separatorDepth γ₂ ε hγ₂ hε ≤ separatorDepth γ₁ ε hγ₁ hε := by
  unfold separatorDepth
  apply Nat.mul_le_mul
  · -- 2 * (numSepLevels γ₂ + 1) + 1 ≤ 2 * (numSepLevels γ₁ + 1) + 1
    have := numSepLevels_antitone hγ₁ h; omega
  · -- halver depth antitone: ε/t₁ ≤ ε/t₂ since t₂ ≤ t₁
    have ht : sepTotalLayers γ₂ ≤ sepTotalLayers γ₁ := by
      unfold sepTotalLayers; have := numSepLevels_antitone hγ₁ h; omega
    have ht₂_pos := sepTotalLayers_pos γ₂
    apply halverDepth_antitone
    exact div_le_div_of_nonneg_left hε.le
      (Nat.cast_pos.mpr ht₂_pos)
      (by exact_mod_cast ht)

end


