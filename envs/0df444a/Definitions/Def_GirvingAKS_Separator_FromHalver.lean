-- Prove2me | Definitions.Def_GirvingAKS_Separator_FromHalver
-- name    : GirvingAKS_Separator_FromHalver
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:37.751514+00:00
-- url     : https://prove2.me/theorems/d0a9899b-9642-4562-9a1c-ff48c445bfa6
-- title:
--   AKS sorting networks (Seiferas port) — Halver → Separator: Induction Step and Assembly
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Separator/FromHalver.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** SepFinal direction helpers, induction step assembly, iterated halving, depth bounds, and the `halverToSeparator_props` bundle. Depends on `FromHalverDefs.lean` for definitions and base lemmas. (Seiferas 2009, Section 6, Lemma 1)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Separator/FromHalver.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Separator_FromHalverDefs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Separator/FromHalver.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Halver → Separator: Induction Step and Assembly

  SepFinal direction helpers, induction step assembly, iterated halving,
  depth bounds, and the `halverToSeparator_props` bundle.
  Depends on `FromHalverDefs.lean` for definitions and base lemmas.
  (Seiferas 2009, Section 6, Lemma 1)
-/


section


open Finset BigOperators


/-! **Induction step: SepFinal direction helpers** -/

/-- Endpoints of non-last-chunk comparators (chunks 0, ..., 2^t-2) are below `n - C`. -/
lemma non_last_chunk_endpoints_below {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ c ∈ ((List.range (2 ^ t - 1)).flatMap (fun k ↦
      let offset := k * C
      if h : offset + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H offset h).comparators
      else [])),
    c.i.val < n - C ∧ c.j.val < n - C := by
  intro C H c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range] at hk_mem
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have h_last_offset : (2 ^ t - 1) * C = n - C := by
    have : (2 ^ t - 1) * C + C = n := by
      calc (2 ^ t - 1) * C + C = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]; ring
        _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
        _ = n := by rw [mul_comm]; exact h_exact
    omega
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [applyHalverToSubinterval, ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    have hkC_bound : k * C + C ≤ n - C := by
      have : (k + 1) * C ≤ (2 ^ t - 1) * C :=
        Nat.mul_le_mul_right C (by omega)
      rw [Nat.add_mul] at this; simp only [Nat.one_mul] at this; omega
    have hci : c₀.i.val < C := by have := hi₀; have := h2H_le_C; omega
    have hcj : c₀.j.val < C := by have := hj₀; have := h2H_le_C; omega
    exact ⟨by dsimp; omega, by dsimp; omega⟩
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Non-crossing at boundary `n - C`: when `2^t ∣ n`, all `halverAtLevel` comparators
    have both endpoints `< n - C` or both `≥ n - C`. -/
lemma halverAtLevel_comparators_non_crossing_last {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (c : Comparator n) (hc : c ∈ (halverAtLevel n halvers t).comparators) :
    let C := n / 2 ^ t
    (c.i.val < n - C ∧ c.j.val < n - C) ∨ (n - C ≤ c.i.val ∧ n - C ≤ c.j.val) := by
  simp only [halverAtLevel, applyHalverToSubinterval] at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, hk_mem, hc_chunk⟩ := hc
  rw [List.mem_range] at hk_mem
  set C := n / 2 ^ t
  set H := C / 2
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have h_last_offset : (2 ^ t - 1) * C = n - C := by
    have : (2 ^ t - 1) * C + C = n := by
      calc (2 ^ t - 1) * C + C = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]; ring
        _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
        _ = n := by rw [mul_comm]; exact h_exact
    omega
  by_cases hguard : k * C + 2 * H ≤ n
  · rw [dif_pos hguard] at hc_chunk
    simp only [ComparatorNetwork.shiftEmbed, List.mem_map] at hc_chunk
    obtain ⟨c₀, _, rfl⟩ := hc_chunk
    have hi₀ := c₀.i.isLt
    have hj₀ := c₀.j.isLt
    by_cases hk_last : k = 2 ^ t - 1
    · right
      have hkC_eq : k * C = n - C := by rw [hk_last]; exact h_last_offset
      exact ⟨by dsimp; omega, by dsimp; omega⟩
    · left
      have hkC_bound : k * C + C ≤ n - C := by
        have : (k + 1) * C ≤ (2 ^ t - 1) * C :=
          Nat.mul_le_mul_right C (by omega)
        rw [Nat.add_mul] at this; simp only [Nat.one_mul] at this; omega
      have hci : c₀.i.val < C := by have := hi₀; have := h2H_le_C; omega
      have hcj : c₀.j.val < C := by have := hj₀; have := h2H_le_C; omega
      exact ⟨by dsimp; omega, by dsimp; omega⟩
  · rw [dif_neg hguard] at hc_chunk; simp at hc_chunk

/-- Count of values `< k` at positions `< n - C` is preserved by `halverAtLevel`.
    Mirror of `halverAtLevel_chunk0_count_eq` for the last-chunk boundary. -/
lemma halverAtLevel_non_last_count_eq {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (k : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w₁ pos).val < k)).card := by
  intro C
  show (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ ((halverAtLevel n halvers t).comparators.foldl
      (fun acc c ↦ c.apply acc) w₁ pos).val < k)).card = _
  exact foldl_preserves_count _ w₁ hw₁ (n - C) k
    (fun c hc => halverAtLevel_comparators_non_crossing_last t h_pow_div c hc)

/-- Local view for the LAST chunk: `halverAtLevel` execution at position `pos`
    in `[n-C, n-C+2H)` equals the last-chunk halver's local execution. -/
lemma halverAtLevel_local_eq_last {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w : Fin n → Fin n) :
    let C := n / 2 ^ t
    let H := C / 2
    ∀ (pos : Fin n) (hge : n - C ≤ pos.val) (hlt : pos.val < n - C + 2 * H),
    have h2H_le : n - C + 2 * H ≤ n := by
      have := Nat.mul_div_le C 2; have := Nat.div_le_self n (2^t); omega
    (halverAtLevel n halvers t).exec w pos =
    (halvers H).exec
      (fun j : Fin (2 * H) ↦ w ⟨(n - C) + j.val, by
        have := j.isLt; have := Nat.div_le_self n (2^t)
        have := Nat.mul_div_le C 2; omega⟩)
      ⟨pos.val - (n - C), by omega⟩ := by
  intro C H pos hge hlt h2H_le
  show (halverAtLevel n halvers t).comparators.foldl (fun acc c ↦ c.apply acc) w pos = _
  unfold halverAtLevel; simp only
  change ((List.range (2 ^ t)).flatMap (fun k ↦
      if h : k * C + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H (k * C) h).comparators
      else [])).foldl (fun acc c ↦ c.apply acc) w pos = _
  have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  have h_exact : C * 2 ^ t = n := Nat.div_mul_cancel h_pow_div
  have h2H_le_C : 2 * H ≤ C := Nat.mul_div_le C 2
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h_last_sum : (2 ^ t - 1) * C + C = n := by
    calc (2 ^ t - 1) * C + C
        = (2 ^ t - 1) * C + 1 * C := by rw [one_mul]
      _ = (2 ^ t - 1 + 1) * C := by rw [Nat.add_mul]
      _ = 2 ^ t * C := by rw [Nat.sub_add_cancel hpow_pos]
      _ = C * 2 ^ t := by rw [mul_comm]
      _ = n := h_exact
  have hoffset_eq : (2 ^ t - 1) * C = n - C := by omega
  have h_split : List.range (2 ^ t) = List.range (2 ^ t - 1) ++ [2 ^ t - 1] := by
    conv_lhs => rw [show 2 ^ t = (2 ^ t - 1) + 1 from by omega]
    exact List.range_succ
  rw [h_split, List.flatMap_append, List.foldl_append]
  set w' := ((List.range (2 ^ t - 1)).flatMap (fun k ↦
      if h : k * C + 2 * H ≤ n then
        (applyHalverToSubinterval n halvers H (k * C) h).comparators
      else [])).foldl (fun acc c ↦ c.apply acc) w with hw'_def
  have hw'_agree : ∀ j : Fin n, n - C ≤ j.val → w' j = w j := by
    intro j hj
    exact foldl_comparators_outside _ w j (fun c hc ↦ by
      have ⟨hi, hj_bound⟩ := non_last_chunk_endpoints_below t h_pow_div c hc
      exact ⟨by intro heq; subst heq; omega, by intro heq; subst heq; omega⟩)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hguard : (2 ^ t - 1) * C + 2 * H ≤ n := by omega
  rw [dif_pos hguard]
  simp only [applyHalverToSubinterval]
  show ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w' pos = _
  have hoffset_le_pos : (2 ^ t - 1) * C ≤ pos.val := by omega
  have hpos_in : pos.val - (2 ^ t - 1) * C < 2 * H := by omega
  have h_shift := ComparatorNetwork.shiftEmbed_exec_inside (halvers H) n
    ((2 ^ t - 1) * C) hguard w' ⟨pos.val - (2 ^ t - 1) * C, hpos_in⟩
  have hfin_eq : ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w'
      ⟨(2 ^ t - 1) * C + (pos.val - (2 ^ t - 1) * C), by omega⟩ =
    ((halvers H).shiftEmbed n ((2 ^ t - 1) * C) hguard).exec w' pos := by
    congr 1; exact Fin.ext (Nat.add_sub_cancel' hoffset_le_pos)
  rw [← hfin_eq, h_shift]
  congr 1
  · funext j
    have hge_j : n - C ≤ (2 ^ t - 1) * C + j.val := by omega
    rw [hw'_agree ⟨(2 ^ t - 1) * C + j.val, by omega⟩ hge_j]
    congr 1; exact Fin.ext (show (2 ^ t - 1) * C + j.val = (n - C) + j.val by rw [hoffset_eq])
  · exact Fin.ext (show pos.val - (2 ^ t - 1) * C = pos.val - (n - C) by rw [hoffset_eq])

/-- Count of values `≥ threshold` at positions `< n - C` is preserved by `halverAtLevel`.
    Derives from `halverAtLevel_non_last_count_eq` via complementary counting. -/
lemma far_outsider_count_preserved_final {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (h_pow_div : 2 ^ t ∣ n)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁) (threshold : ℕ) :
    let C := n / 2 ^ t
    let w₂ := (halverAtLevel n halvers t).exec w₁
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w₁ pos).val)).card := by
  intro C w₂
  have hpart : ∀ w : Fin n → Fin n,
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ (w pos).val < threshold)).card +
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C ∧ threshold ≤ (w pos).val)).card =
      (Finset.univ.filter (fun pos : Fin n ↦ pos.val < n - C)).card := by
    intro w
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hlt : (w pos).val < threshold
        · left; exact ⟨h, hlt⟩
        · right; exact ⟨h, by omega⟩
    · rw [Finset.disjoint_filter]; intro _ _ ⟨_, h1⟩ ⟨_, h2⟩; omega
  have hlt_eq := halverAtLevel_non_last_count_eq (halvers := halvers) t h_pow_div w₁ hw₁ threshold
  change (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ (w₂ pos).val < threshold)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - C ∧ (w₁ pos).val < threshold)).card at hlt_eq
  linarith [hpart w₂, hpart w₁]

/-- Near outsider bound for the FINAL direction: positions in `[n-C, n-H)` of
    the last chunk with large output values are bounded by `ε₁ * a`. -/
lemma halverAtLevel_near_outsider_le_final {n : ℕ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} {ε₁ : ℝ} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁)
    (hhalver : IsEpsilonHalver (halvers ((n / 2 ^ t) / 2)) ε₁) (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t) (h_pow_div : 2 ^ t ∣ n)
    (k : ℕ) (hk : k ≤ n / 2 ^ t / 2) :
    let C := n / 2 ^ t
    let H := C / 2
    let w₂ := (halverAtLevel n halvers t).exec w₁
    let a := (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card
    ((Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ ε₁ * ↑a := by
  intro C H w₂ a
  have h2H_eq : 2 * H = C := by have := Nat.div_mul_cancel h_even; omega
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h2H_le_n : 2 * H ≤ n := by omega
  -- Trivial when H = 0
  by_cases hH : H = 0
  · have hC0 : C = 0 := by omega
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨_, h, _⟩; omega
    rw [hempty]; simp; exact mul_nonneg hε₁ (Nat.cast_nonneg _)
  · -- H > 0
    have hH_pos : 0 < H := Nat.pos_of_ne_zero hH
    have h2H_pos : 0 < 2 * H := by omega
    -- Local restriction u : Fin (2*H) → Fin n
    set u : Fin (2 * H) → Fin n :=
      fun j ↦ w₁ ⟨(n - C) + j.val, by have := j.isLt; omega⟩ with hu_def
    have hu_inj : Function.Injective u := by
      intro j₁ j₂ heq
      have h := hw₁ heq
      exact Fin.ext (by have := congr_arg Fin.val h; dsimp at this; omega)
    -- ha_eq: count a on Fin (2*H) = count a on Fin n restricted to [n-C, n)
    have ha_eq : a = (Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        show n - k ≤ (u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        have heq : (⟨(n - C) + (pos.val - (n - C)), (by omega)⟩ : Fin n) = pos := by
          ext; show (n - C) + (pos.val - (n - C)) = pos.val; omega
        rw [heq]; exact hpos.2
      · intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨by omega, hi⟩
      · intro pos hpos
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    -- a ≤ H
    have ha_le : (Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card ≤ H := by
      calc _ ≤ k := injective_count_ge_le u hu_inj k
        _ ≤ H := hk
    -- hcard_eq: LHS on Fin n = LHS on Fin (2*H)
    have hcard_eq : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
      (Finset.univ.filter (fun pos : Fin (2 * H) ↦
        pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · -- forward
        intro pos hpos
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        refine ⟨by show pos.val - (n - C) < H; omega, ?_⟩
        -- Use halverAtLevel_local_eq_last
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁ pos hpos.1
          (show pos.val < n - C + 2 * H by omega)
        show n - k ≤ ((halvers H).exec u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        rw [← hlocal]; exact hpos.2.2
      · -- backward
        intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨hi_lt, hi_val⟩ := hi
        refine ⟨by omega, offset_add_lt_sub h2H_eq hC_le_n hi_lt, ?_⟩
        change n - k ≤ ((halverAtLevel n halvers t).exec w₁ ⟨(n - C) + i.val, _⟩).val
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁
          (⟨(n - C) + i.val, by have := i.isLt; omega⟩ : Fin n)
          (show n - C ≤ (n - C) + i.val from by omega)
          (show (n - C) + i.val < n - C + 2 * H from by have := i.isLt; omega)
        rw [hlocal]
        have hfin : (⟨(n - C) + i.val - (n - C), (by omega)⟩ : Fin (2 * H)) = i := by
          ext; show (n - C) + i.val - (n - C) = i.val; omega
        rw [hfin]
        exact hi_val
      · -- left inverse
        intro pos hpos
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · -- right inverse
        intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    -- Apply halver_injective_final_halved
    have hhalved := halver_injective_final_halved hhalver hε₁ u hu_inj (n - k) ha_le
    calc ((Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ)
        = ↑(Finset.univ.filter (fun pos : Fin (2 * H) ↦
            pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
          exact_mod_cast hcard_eq
      _ ≤ ε₁ * ↑(Finset.univ.filter (fun i : Fin (2 * H) ↦ n - k ≤ (u i).val)).card := hhalved
      _ = ε₁ * ↑a := by rw [← ha_eq]


/-! **Induction step: SepFinal assembly** -/

/-- SepFinal direction of the halving step. -/
lemma separator_halving_step_final {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : IsEpsilonHalver (halvers ((n / 2 ^ t) / 2)) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (h_pow_div : 2 ^ t ∣ n)
    (v : Equiv.Perm (Fin n)) :
    SepFinal
      ((⟨net.comparators ++ (halverAtLevel n halvers t).comparators⟩ :
        ComparatorNetwork n).exec (v : Fin n → Fin n))
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  rw [ComparatorNetwork.exec_append]
  set w₁ := net.exec (v : Fin n → Fin n) with hw₁_def
  have hw₁_inj : Function.Injective w₁ :=
    ComparatorNetwork.exec_injective net (Equiv.injective v)
  set w₂ := (halverAtLevel n halvers t).exec w₁ with hw₂_def
  set C := n / 2 ^ t with hC_def
  set H := C / 2 with hH_def
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have hH_le_C : H ≤ C := Nat.div_le_self C 2
  show SepInitial (α := (Fin n)ᵒᵈ) _ _ _
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od, rank_fin_od_fin]
  rw [floor_pow_half_eq_div n (t + 1), ← half_chunk_eq n t]
  set k := ⌊γ' * (n : ℝ)⌋₊ with hk_def
  have hk_le : k ≤ H := by
    calc k ≤ n / 2 ^ (t + 1) := floor_gamma_le_div_pow n (t + 1) γ' hγ' hγ'_le
      _ = H := (half_chunk_eq n t).symm
  suffices h : ((Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ (ε' + ε₁) * γ' * ↑n by
    calc ((Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
          H ≤ n - 1 - (pos : Fin n).val ∧
          n - 1 - (w₂ pos : Fin n).val < k)).card : ℝ)
        = ((Finset.univ.filter (fun pos : Fin n ↦
            pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) := by
          congr 1
          apply Finset.card_nbij'
            (fun a : (Fin n)ᵒᵈ ↦ (a : Fin n))
            (fun b : Fin n ↦ (b : (Fin n)ᵒᵈ))
          · intro a ha
            simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
            exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by dsimp only; have := (a : Fin n).isLt; omega,
              by dsimp only; have := (w₂ a : Fin n).isLt; omega⟩)
          · intro b hb
            have ⟨hb1, hb2⟩ := (Finset.mem_filter.mp hb).2
            exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by dsimp only at hb1 ⊢; have := b.isLt; omega,
              by dsimp only at hb2 ⊢; have := (w₂ b).isLt; omega⟩)
          · intro _ _; rfl
          · intro _ _; rfl
      _ ≤ _ := h
  have hpart : (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card +
    (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ⟨hlt, hval⟩
        by_cases hpos : n - C ≤ pos.val
        · left; exact ⟨hpos, hlt, hval⟩
        · right; exact ⟨by omega, hval⟩
      · rintro (⟨_, hlt, hval⟩ | ⟨hlt, hval⟩)
        · exact ⟨hlt, hval⟩
        · exact ⟨by omega, hval⟩
    · rw [Finset.disjoint_filter]
      intro pos _ ⟨hge, _, _⟩ ⟨hlt, _⟩; omega
  have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤
    ε₁ * ↑(Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card := by
    rw [hw₂_def]
    exact halverAtLevel_near_outsider_le_final t w₁ hw₁_inj hhalver hε₁ h_even h_pow_div k hk_le
  have hfar_eq : (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card := by
    rw [hw₂_def]; exact far_outsider_count_preserved_final t h_pow_div w₁ hw₁_inj (n - k)
  have hγ'_le_t : γ' ≤ 1 / 2 ^ t := by
    calc γ' ≤ 1 / 2 ^ (t + 1) := hγ'_le
      _ ≤ 1 / 2 ^ t :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) < 2 ^ t)
          (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ t))
  have hsep_far : ((Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card : ℝ) ≤ ε' * γ' * ↑n := by
    have hfinal := (hsep v).2 γ' hγ' hγ'_le_t
    simp only [Fintype.card_orderDual, Fintype.card_fin, rank_fin_od, rank_fin_od_fin] at hfinal
    rw [floor_pow_half_eq_div n t, ← hw₁_def, ← hk_def] at hfinal
    have hconv : (Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
        C ≤ n - 1 - (pos : Fin n).val ∧
        n - 1 - (w₁ pos : Fin n).val < k)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card := by
      apply Finset.card_nbij'
        (fun a : (Fin n)ᵒᵈ ↦ (a : Fin n))
        (fun b : Fin n ↦ (b : (Fin n)ᵒᵈ))
      · intro a ha
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by dsimp only; have := (a : Fin n).isLt; omega,
          by dsimp only; have := (w₁ a : Fin n).isLt; omega⟩)
      · intro b hb
        have ⟨hb1, hb2⟩ := (Finset.mem_filter.mp hb).2
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by dsimp only at hb1 ⊢; have := b.isLt; omega,
          by dsimp only at hb2 ⊢; have := (w₁ b).isLt; omega⟩)
      · intro _ _; rfl
      · intro _ _; rfl
    rw [← hconv]; exact hfinal
  set a := (Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card with ha_def
  have ha_le_k : a ≤ k := by
    calc a ≤ (Finset.univ.filter (fun pos : Fin n ↦ n - k ≤ (w₁ pos).val)).card := by
          apply Finset.card_le_card; intro pos
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact And.right
      _ ≤ k := injective_count_ge_le w₁ hw₁_inj k
  have ha_le : (a : ℝ) ≤ γ' * ↑n := by
    calc (a : ℝ) ≤ ↑k := by exact_mod_cast ha_le_k
      _ ≤ γ' * ↑n := Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
  calc ((Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ)
      = ↑(Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card +
        ↑(Finset.univ.filter (fun pos : Fin n ↦
          pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card := by exact_mod_cast hpart
    _ ≤ ε₁ * ↑a + ε' * γ' * ↑n := by
        have : ((Finset.univ.filter (fun pos : Fin n ↦
            pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ ε' * γ' * ↑n := by
          rw [hfar_eq]; exact hsep_far
        linarith [hnear]
    _ ≤ ε₁ * (γ' * ↑n) + ε' * γ' * ↑n := by
        linarith [mul_le_mul_of_nonneg_left ha_le hε₁]
    _ = (ε' + ε₁) * γ' * ↑n := by ring


/-! **Induction step: assembly** -/

/-- SepInitial direction of the halving step. -/
lemma separator_halving_step_initial {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : IsEpsilonHalver (halvers ((n / 2 ^ t) / 2)) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (v : Equiv.Perm (Fin n)) :
    SepInitial
      ((⟨net.comparators ++ (halverAtLevel n halvers t).comparators⟩ :
        ComparatorNetwork n).exec (v : Fin n → Fin n))
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  rw [ComparatorNetwork.exec_append]
  set w₁ := net.exec (v : Fin n → Fin n) with hw₁_def
  have hw₁_inj : Function.Injective w₁ :=
    ComparatorNetwork.exec_injective net (Equiv.injective v)
  intro γ' hγ' hγ'_le
  simp only [Fintype.card_fin, rank_fin_val]
  rw [floor_pow_half_eq_div n (t + 1), ← half_chunk_eq n t]
  set k := ⌊γ' * (n : ℝ)⌋₊ with hk_def
  set w₂ := (halverAtLevel n halvers t).exec w₁ with hw₂_def
  have hk_le : k ≤ n / 2 ^ t / 2 := by
    calc k ≤ n / 2 ^ (t + 1) := floor_gamma_le_div_pow n (t + 1) γ' hγ' hγ'_le
      _ = n / 2 ^ t / 2 := (half_chunk_eq n t).symm
  -- Split {pos ≥ n/2^t/2 : w₂(pos) < k} into near [n/2^t/2, n/2^t) and far [n/2^t, n)
  have hpart : (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card +
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ⟨hge, hlt⟩
        by_cases hpos : pos.val < n / 2 ^ t
        · left; exact ⟨hge, hpos, hlt⟩
        · right; exact ⟨by omega, hlt⟩
      · rintro (⟨hge, _, hlt⟩ | ⟨hge, hlt⟩)
        · exact ⟨hge, hlt⟩
        · exact ⟨le_trans (Nat.div_le_self _ 2) hge, hlt⟩
    · rw [Finset.disjoint_filter]
      intro pos _ ⟨_, hlt, _⟩ ⟨hge, _⟩; omega
  -- Near outsider bound
  have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card : ℝ) ≤
    ε₁ * ↑(Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n / 2 ^ t ∧ (w₁ pos).val < k)).card := by
    rw [hw₂_def]
    exact halverAtLevel_near_outsider_le t w₁ hw₁_inj hhalver hε₁ h_even k hk_le
  -- Far outsider preservation
  have hfar_eq : (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card =
    (Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₁ pos).val < k)).card := by
    rw [hw₂_def]; exact far_outsider_count_preserved t w₁ hw₁_inj k
  -- γ' ≤ 1/2^t
  have hγ'_le_t : γ' ≤ 1 / 2 ^ t := by
    calc γ' ≤ 1 / 2 ^ (t + 1) := hγ'_le
      _ ≤ 1 / 2 ^ t :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) < 2 ^ t)
          (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ t))
  -- From hsep: far outsiders bounded by ε' * γ' * n
  have hsep_far : ((Finset.univ.filter (fun pos : Fin n ↦
      n / 2 ^ t ≤ pos.val ∧ (w₁ pos).val < k)).card : ℝ) ≤ ε' * γ' * ↑n := by
    have h := (hsep v).1 γ' hγ' hγ'_le_t
    simp only [Fintype.card_fin, rank_fin_val] at h
    rw [floor_pow_half_eq_div n t, ← hw₁_def, ← hk_def] at h
    exact h
  -- a = count at positions < n/2^t with values < k
  set a := (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < n / 2 ^ t ∧ (w₁ pos).val < k)).card with ha_def
  have ha_le_k : a ≤ k := by
    calc a ≤ (Finset.univ.filter (fun pos : Fin n ↦ (w₁ pos).val < k)).card := by
          apply Finset.card_le_card; intro pos
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact And.right
      _ ≤ k := injective_count_lt_le w₁ hw₁_inj k
  have ha_le : (a : ℝ) ≤ γ' * ↑n := by
    calc (a : ℝ) ≤ ↑k := by exact_mod_cast ha_le_k
      _ ≤ γ' * ↑n := Nat.floor_le (mul_nonneg hγ' (Nat.cast_nonneg _))
  calc ((Finset.univ.filter (fun pos : Fin n ↦
        n / 2 ^ t / 2 ≤ pos.val ∧ (w₂ pos).val < k)).card : ℝ)
      = ↑(Finset.univ.filter (fun pos : Fin n ↦
          n / 2 ^ t / 2 ≤ pos.val ∧ pos.val < n / 2 ^ t ∧ (w₂ pos).val < k)).card +
        ↑(Finset.univ.filter (fun pos : Fin n ↦
          n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card := by exact_mod_cast hpart
    _ ≤ ε₁ * ↑a + ε' * γ' * ↑n := by
        have : ((Finset.univ.filter (fun pos : Fin n ↦
            n / 2 ^ t ≤ pos.val ∧ (w₂ pos).val < k)).card : ℝ) ≤ ε' * γ' * ↑n := by
          rw [hfar_eq]; exact hsep_far
        linarith [hnear]
    _ ≤ ε₁ * (γ' * ↑n) + ε' * γ' * ↑n := by
        linarith [mul_le_mul_of_nonneg_left ha_le hε₁]
    _ = (ε' + ε₁) * γ' * ↑n := by ring

/-- Halving refines separation: given (1/2^t, ε')-separation, applying
    ε₁-halvers at level `t` gives (1/2^(t+1), ε' + ε₁)-separation.

    Requires `2 ∣ n / 2^t` (chunk size is even) so that `2 * halfChunk`
    covers the full chunk — without this, the last position of each chunk
    is uncovered and can strand a small value (confirmed counterexample:
    n=3, t=0 with perfect halvers).

    The level must match the separation parameter (γ = 1/2^t aligns with
    chunk size n/2^t at level t). Within each chunk, the halver pushes
    the smaller half to the first half-chunk, creating the finer boundary.

    Error analysis (SepInitial direction, γ' ≤ 1/2^(t+1)):
    • Positions ≥ n/2^t (other chunks): unchanged from old separation → ≤ ε'·γ'·n
    • Positions [n/2^(t+1), n/2^t) (second half of chunk 0): by the halver's
      EpsilonInitialHalved, at most ε₁·a displaced, where a ≤ k = ⌊γ'n⌋.
    Total: (ε' + ε₁)·γ'·n. SepFinal is symmetric.
    (Seiferas 2009, Section 6, proof of Lemma 1) -/
theorem separator_halving_step {n : ℕ} {ε' ε₁ : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSeparator net (1 / 2 ^ t) ε')
    (hhalver : IsEpsilonHalver (halvers ((n / 2 ^ t) / 2)) ε₁)
    (hε₁ : 0 ≤ ε₁)
    (h_even : 2 ∣ n / 2 ^ t)
    (h_pow_div : 2 ^ t ∣ n) :
    IsSeparator
      { comparators := net.comparators ++ (halverAtLevel n halvers t).comparators }
      (1 / 2 ^ (t + 1))
      (ε' + ε₁) := by
  intro v
  exact ⟨separator_halving_step_initial t hsep hhalver hε₁ h_even v,
         separator_halving_step_final t hsep hhalver hε₁ h_even h_pow_div v⟩


/-! **Iterated halving** -/

/-- `rank a < Fintype.card α` for any element in a finite linear order. -/
lemma rank_lt_card {α : Type*} [Fintype α] [LinearOrder α] (a : α) :
    rank a < Fintype.card α := by
  unfold rank; apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨a, Finset.mem_univ a, by simp⟩

/-- `SepInitial` is trivially true at γ = 1: the threshold `⌊1·n⌋₊ = n` exceeds
    every rank, so the filter is empty and any ε bound (including 0) holds. -/
lemma sepInitial_one_zero {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) : SepInitial w 1 0 := by
  intro γ' hγ' _
  suffices h : (Finset.univ.filter (fun pos : α ↦
      ⌊(1 : ℝ) * ↑(Fintype.card α)⌋₊ ≤ rank pos ∧
      rank (w pos) < ⌊γ' * ↑(Fintype.card α)⌋₊)).card = 0 by
    push_cast [h]; positivity
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  have hr := rank_lt_card x
  simp only [one_mul, Nat.floor_natCast] at hx
  omega

/-- `halverToSeparator` at `t + 1` decomposes into level-`t` separator concatenated
    with level-`t` halvers. -/
lemma halverToSeparator_succ_eq {ε : ℚ}
    (n : ℕ) (family : HalverFamily ε) (t : ℕ) :
    halverToSeparator n family (t + 1) =
    ⟨(halverToSeparator n family t).comparators ++
     (halverAtLevel n family.net t).comparators⟩ := by
  simp only [halverToSeparator, halverNetwork, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

/-- `t` levels of iterated ε-halving give (t·ε)-approximate (1/2^t)-separation.

    Requires `2 ^ t ∣ n` to ensure all chunk sizes at levels 0, ..., t-1
    are even (needed by `separator_halving_step`). This is satisfied when
    n is a power of 2 ≥ 2^t, as in the standard AKS construction.

    Proof: induction on `t` using `sepInitial_one_zero` (base) and
    `separator_halving_step` (step). At each level, the halver introduces
    ε error (one application of EpsilonInitialHalved + EpsilonFinalHalved),
    giving +ε per level, total t·ε.
    (Seiferas 2009, Section 6, Lemma 1) -/
theorem halverToSeparator_isSeparator {ε : ℚ}
    (n : ℕ) (family : HalverFamily ε) (t : ℕ) (hε : 0 ≤ (ε : ℝ))
    (h_div : 2 ^ t ∣ n)
    (h_sizes : ∀ level, level < t → 0 < (n / 2 ^ level) / 2) :
    IsSeparator (halverToSeparator n family t) (1 / 2 ^ t) (↑t * ↑ε) := by
  induction t with
  | zero =>
    simp only [halverToSeparator, halverNetwork, List.range_zero, List.flatMap_nil,
      pow_zero, Nat.cast_zero, zero_mul, div_one]
    intro v; rw [show (⟨[]⟩ : ComparatorNetwork n).exec (v : Fin n → Fin n) = v from by
      simp [ComparatorNetwork.exec]]
    exact ⟨sepInitial_one_zero _, sepInitial_one_zero _⟩
  | succ t ih =>
    have h_div_t : 2 ^ t ∣ n := dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ t)) h_div
    have h_even : 2 ∣ n / 2 ^ t := by
      rw [pow_succ] at h_div; obtain ⟨k, hk⟩ := h_div
      rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
      exact dvd_mul_right 2 k
    rw [halverToSeparator_succ_eq]
    have hstep := separator_halving_step t
      (ih h_div_t (fun level hlevel => h_sizes level (by omega)))
      (family.isHalver _) hε h_even h_div_t
    convert hstep using 1
    push_cast; ring


/-! **Depth bound** -/

/-- Per-level depth bound: halvers at one tree level operate on disjoint
    wire ranges (different sub-intervals), so they run in parallel. -/
theorem halverAtLevel_depth_le {d : ℕ}
    (n : ℕ) (halvers : (m : ℕ) → ComparatorNetwork (2 * m))
    (h_depth : ∀ m, (halvers m).depth ≤ d) (level : ℕ) :
    (halverAtLevel n halvers level).depth ≤ d := by
  unfold halverAtLevel applyHalverToSubinterval
  apply depth_flatMap_disjoint
  · -- Per-chunk depth ≤ d
    intro k _; simp only
    split
    · rename_i h
      exact le_trans (depth_shiftEmbed_le _ _ _ h) (h_depth _)
    · simp [ComparatorNetwork.depth]
  · -- Pairwise wire disjointness: chunks at offsets k₁*C, k₂*C have non-overlapping
    -- wire ranges [ki*C, ki*C + 2*H) since 2*H ≤ C and k₁ < k₂.
    exact List.pairwise_lt_range.imp fun {k₁ k₂} (hlt : k₁ < k₂) ↦ by
      simp only
      intro c₁ hc₁ c₂ hc₂
      -- Case-split on whether each chunk's dite condition holds
      by_cases h₁ : k₁ * (n / 2 ^ level) + 2 * (n / 2 ^ level / 2) ≤ n
      · by_cases h₂ : k₂ * (n / 2 ^ level) + 2 * (n / 2 ^ level / 2) ≤ n
        · -- Both conditions hold; extract the base comparators
          simp only [h₁, h₂, dite_true, ComparatorNetwork.shiftEmbed,
            List.mem_map] at hc₁ hc₂
          obtain ⟨c₁₀, _, rfl⟩ := hc₁; obtain ⟨c₂₀, _, rfl⟩ := hc₂
          have h1i := c₁₀.i.isLt; have h1j := c₁₀.j.isLt
          have h2i := c₂₀.i.isLt; have h2j := c₂₀.j.isLt
          -- Key nonlinear facts for omega (products of variables)
          have hCb : 2 * (n / 2 ^ level / 2) ≤ n / 2 ^ level :=
            Nat.mul_div_le _ 2
          have hk : k₁ * (n / 2 ^ level) + (n / 2 ^ level) ≤
              k₂ * (n / 2 ^ level) := by
            have := Nat.mul_le_mul_right (n / 2 ^ level) hlt
            rw [Nat.succ_mul] at this; exact this
          constructor <;> constructor <;> intro heq <;> {
            simp only [Fin.mk.injEq] at heq; omega }
        · simp only [h₂, dite_false] at hc₂
          exact absurd hc₂ (List.not_mem_nil)
      · simp only [h₁, dite_false] at hc₁
        exact absurd hc₁ (List.not_mem_nil)

/-- Iterated separator depth ≤ t · d. At each of `t` levels, halvers at the
    same level operate on disjoint wire ranges, giving depth ≤ d per level.
    Levels are sequential (concatenated), so total depth ≤ t · d. -/
theorem halverToSeparator_depth_le {ε : ℚ}
    (n : ℕ) (family : HalverFamily ε) (t : ℕ) :
    (halverToSeparator n family t).depth ≤ t * family.depth := by
  unfold halverToSeparator halverNetwork
  induction t with
  | zero => simp [ComparatorNetwork.depth]
  | succ t ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have h_app := depth_append
      (⟨(List.range t).flatMap fun l ↦
        (halverAtLevel n family.net l).comparators⟩)
      (halverAtLevel n family.net t)
    have h_level := halverAtLevel_depth_le n family.net
      family.depth_le t
    linarith


/-! **Bundle into SeparatorFamily** -/

/-- Separator property for a specific `n` with divisibility.
    Use this instead of `SeparatorFamily` when the divisibility condition
    `2 ^ t ∣ n` is not universally satisfied.
    (Seiferas 2009, Section 6, Lemma 1) -/
theorem halverToSeparator_props {ε : ℚ}
    (family : HalverFamily ε)
    (n t : ℕ) (hε : 0 ≤ (ε : ℝ)) (h_div : 2 ^ t ∣ n)
    (h_sizes : ∀ level, level < t → 0 < (n / 2 ^ level) / 2) :
    IsSeparator (halverToSeparator n family t) (1 / 2 ^ t) (↑t * ↑ε) ∧
    (halverToSeparator n family t).depth ≤ t * family.depth :=
  ⟨halverToSeparator_isSeparator n family t hε h_div h_sizes,
   halverToSeparator_depth_le n family t⟩


/-! **Separator Family from Halver Family** -/

end


