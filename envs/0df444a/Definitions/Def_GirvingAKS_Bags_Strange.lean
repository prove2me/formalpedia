-- Prove2me | Definitions.Def_GirvingAKS_Bags_Strange
-- name    : GirvingAKS_Bags_Strange
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:23:25.58819+00:00
-- url     : https://prove2.me/theorems/b74a1597-a016-4d74-bbf4-8b6a31b89d66
-- title:
--   AKS sorting networks (Seiferas port) — Stranger Bound (4th Invariant Condition)
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Strange.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves the stranger bound: at every stage t, the number of j-strangers in each bag is bounded by `γ · ε^(j-1) · capacity(p, k, t, l)`.
--
--   This is the 4th invariant condition of Seiferas (2009), Section 5.
--
--   Key theorem: `stranger_bound`
--
--   Infrastructure is split across:
--
--   - `Filter.lean` — comparator filter/range preservation, separator-quality lemmas
--   - `SepBridge.lean` — separator-stranger bridge, `separator_filter_strangers`
--   - `Subtree.lean` — local subregs lemmas, `spillover_bound`, `subtree_non_native_bound`
--   - `Source3.lean` — j=1 parent stranger bound (`parent_stranger_eq1_le`)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Strange.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Source3

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Strange.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Stranger Bound (4th Invariant Condition)

  Proves the stranger bound: at every stage t, the number of j-strangers in
  each bag is bounded by `γ · ε^(j-1) · capacity(p, k, t, l)`.

  This is the 4th invariant condition of Seiferas (2009), Section 5.

  Key theorem: `stranger_bound`

  Infrastructure is split across:
  - `Filter.lean` — comparator filter/range preservation, separator-quality lemmas
  - `SepBridge.lean` — separator-stranger bridge, `separator_filter_strangers`
  - `Subtree.lean` — local subregs lemmas, `spillover_bound`, `subtree_non_native_bound`
  - `Source3.lean` — j=1 parent stranger bound (`parent_stranger_eq1_le`)
-/


section


open Finset

variable {k : ℕ}

/-! **Base Case** -/

/-- At stage 0, the empty network hasn't been applied, so `perm = perm₀`.
    All registers are at the root bag. For j ≥ 1, every item is native to
    the root's ancestor (which wraps to root), so there are 0 strangers.
    For non-root bags, the register set is empty. -/
theorem stranger_bound_zero (p : Params) (k : ℕ) (_ : 3 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k)) :
    let perm := (stages p k 0).net.exec perm₀
    ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j perm
        ((stages p k 0).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k 0 b.l := by
  intro perm b j hj
  -- perm = perm₀ since stage 0 has empty network
  have hperm : perm = perm₀ := by
    show (stages p k 0).net.exec perm₀ = perm₀
    simp [stages, Build.net_pure, ComparatorNetwork.exec]
  rw [hperm]
  simp only [stages, Build.value_pure]
  by_cases hroot : b.l = 0 ∧ b.x = 0
  · -- Root bag: all items, but no strangers for j ≥ 1
    obtain ⟨hl0, hx0⟩ := hroot
    have hregs : (start k).regs b = univ := by
      simp only [start]; rw [if_pos ⟨hl0, hx0⟩]
    rw [hregs]
    -- For j ≥ 1, ancestor (j-1) has level 0 and idx 0 (= root).
    -- Every item is native to root, so Strange j r perm₀ = False.
    have hzero : b.strangers j perm₀ univ = 0 := by
      simp only [Bag.strangers]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _
      simp only [Bag.Strange, show j ≠ 0 from by omega, false_or]
      intro habs; apply habs
      simp only [Bag.Native, nativeBagIdx]
      have hal : (b.ancestor (j - 1)).l = 0 := by show b.l - (j - 1) = 0; omega
      have hax : (b.ancestor (j - 1)).x = 0 := by show b.x / 2 ^ (j - 1) = 0; rw [hx0]; simp
      rw [hal, hax]; simp [bagSize]
    rw [hzero]; simp only [Nat.cast_zero]
    exact mul_nonneg (mul_nonneg p.hγ_pos.le (pow_nonneg p.hε_pos.le _))
      (capacity_nonneg p k 0 b.l)
  · -- Non-root bag: empty register set
    have hregs : (start k).regs b = ∅ := by
      simp only [start]; rw [if_neg hroot]
    rw [hregs, Bag.strangers_empty]; simp only [Nat.cast_zero]
    exact mul_nonneg (mul_nonneg p.hγ_pos.le (pow_nonneg p.hε_pos.le _))
      (capacity_nonneg p k 0 b.l)

/-! **Arithmetic Lemmas** -/

/-- Core arithmetic for j ≥ 2: children kick + parent contribution ≤ capacity decay.
    `2·γ·ε^j·A·cap + γ·ε^(j-1)·cap/A ≤ γ·ε^(j-1)·ν·cap` by C4_gt1. -/
theorem stranger_gt1_arith {p : Params}
    {cap : ℚ} (hcap : 0 ≤ cap) {j : ℕ} (hj : 2 ≤ j) :
    2 * p.γ * p.ε ^ j * (p.A * cap) +
    p.γ * p.ε ^ (j - 1) * (cap / p.A) ≤
    p.γ * p.ε ^ (j - 1) * (p.ν * cap) := by
  have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
  have hpow : p.ε ^ j = p.ε ^ (j - 1) * p.ε := by
    conv_lhs => rw [show j = (j - 1) + 1 from by omega]; exact pow_succ p.ε (j - 1)
  rw [hpow]
  suffices h : 0 ≤ p.γ * p.ε ^ (j - 1) * cap * (p.ν - (2 * p.A * p.ε + 1 / p.A)) by
    have : p.γ * p.ε ^ (j - 1) * (p.ν * cap) -
        (2 * p.γ * (p.ε ^ (j - 1) * p.ε) * (p.A * cap) +
         p.γ * p.ε ^ (j - 1) * (cap / p.A))
      = p.γ * p.ε ^ (j - 1) * cap * (p.ν - (2 * p.A * p.ε + 1 / p.A)) := by
      field_simp
    linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg p.hγ_pos.le (pow_nonneg p.hε_pos.le _)) hcap)
    (by linarith [p.hC4_gt1])

/-- Core arithmetic for j = 1: children kick + parent contribution ≤ capacity decay.
    Uses the paper-exact bound with `1/(8A³-2A)`. -/
theorem stranger_eq1_arith {p : Params}
    {cap : ℚ} (hcap : 0 ≤ cap) :
    2 * p.γ * p.ε * (p.A * cap) +
    (p.ε * p.γ / p.A + p.ε / (2 * p.A)
     + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
     + 1 / (8 * p.A ^ 3 - 2 * p.A)
     + p.γ / p.A
     + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap ≤
    p.γ * (p.ν * cap) := by
  calc 2 * p.γ * p.ε * (p.A * cap) +
       (p.ε * p.γ / p.A + p.ε / (2 * p.A)
        + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
        + 1 / (8 * p.A ^ 3 - 2 * p.A)
        + p.γ / p.A
        + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap
      = (2 * p.γ * p.ε * p.A
         + p.ε * p.γ / p.A + p.ε / (2 * p.A)
         + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
         + 1 / (8 * p.A ^ 3 - 2 * p.A)
         + p.γ / p.A
         + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by ring
    _ ≤ (p.γ * p.ν) * cap := mul_le_mul_of_nonneg_right p.hC4_eq1 hcap
    _ = p.γ * (p.ν * cap) := by ring

/-! **Root Helper** -/

/-- At the root (level 0) with k ≥ 1, the fringe is 0 and the card is even,
    so split sends nothing to toParent (the middle covers all items). -/
theorem root_toParent_empty (p : Params) (k : ℕ) (hk : 1 ≤ k)
    (t : ℕ) :
    (split ((stages p k t).value.regs (Bag.root k))
      (fringe p k t (Bag.root k).l ((stages p k t).value.regs (Bag.root k)).card)).toParent = ∅ := by
  have hcard : ((stages p k t).value.regs (Bag.root k)).card = bagCard p k t 0 :=
    bagCard_eq_card p k t (Bag.root k)
  have heven : 2 ∣ bagCard p k t 0 := bagCard_root_even p k hk t
  have hf : fringe p k t (Bag.root k).l ((stages p k t).value.regs (Bag.root k)).card = 0 := by
    show fringe p k t 0 _ = 0; simp [fringe]
  rw [hf]
  rw [← Finset.card_eq_zero]
  rw [split_toParent_card, splitParentCard_zero, hcard]
  exact Nat.dvd_iff_mod_eq_zero.mp heven

/-! **Stages Unfolding** -/

/-- Unfold `(stages p k (t+1)).value.regs b` to `stageRegs splitOf b`. -/
theorem stages_succ_regs (p : Params) (k : ℕ)
    (t : ℕ) (b : Bag k) :
    (stages p k (t + 1)).value.regs b =
    let pl := (stages p k t).value
    stageRegs (fun c ↦ split (pl.regs c) (fringe p k t c.l (pl.regs c).card)) b := by
  show (do let pl ← stages p k t; stage p pl t).value.regs b = _
  simp only [Build.value_bind]
  show (stage p (stages p k t).value t).value.regs b = _
  unfold stage separateAndSplit separate
  simp only [Build.value_bind, Build.value_pure]

/-! **Inductive Step** -/

/-- Stranger bound at stage `t+1`, given the bound at stage `t`.

    The proof decomposes each bag's new register set (via `stageRegs`) into
    items from children (kicks) and items from parent, bounds each source
    using the helper lemmas, then combines using C4 arithmetic.

    Dependencies:
    - `strangers_stage_invariant` (used in `kick_stranger_le`)
    - `parent_stranger_j2_le` (separator ε-filtering for j ≥ 2)
    - `parent_stranger_eq1_le` (separator + equidistribution for j = 1) -/
theorem stranger_bound_succ (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ht : t ≤ numStages p k)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j ((stages p k t).net.exec perm₀)
        ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l) :
    let perm := (stages p k (t + 1)).net.exec perm₀
    ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j perm
        ((stages p k (t + 1)).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k (t + 1) b.l := by
  intro perm b j hj
  -- Unfold stages(t+1) to stageRegs
  rw [stages_succ_regs]
  set pl := (stages p k t).value with hpl_def
  set splitOf := fun c : Bag k ↦ split (pl.regs c) (fringe p k t c.l (pl.regs c).card)
    with hsplitOf_def
  -- capacity at t+1 = ν · capacity at t
  rw [capacity_stage_succ]
  set cap := capacity p k t b.l with hcap_def
  -- Nonneg facts
  have hcap_nn : (0 : ℚ) ≤ cap := capacity_nonneg p k t b.l
  have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
  -- Unfold stageRegs to fromChildren ∪ fromParent and apply union bound
  simp only [stageRegs]
  -- Bound on fromChildren
  have hfc : (b.strangers j perm
      (if h : b.l < k then
        (splitOf (b.left h)).toParent ∪ (splitOf (b.right h)).toParent
      else ∅) : ℚ) ≤ 2 * p.γ * p.ε ^ j * (p.A * cap) := by
    by_cases hlk : b.l < k
    · rw [dif_pos hlk]
      -- Union bound on left + right kicks
      calc (b.strangers j perm
              ((splitOf (b.left hlk)).toParent ∪ (splitOf (b.right hlk)).toParent) : ℚ)
          ≤ ↑(b.strangers j perm (splitOf (b.left hlk)).toParent) +
            ↑(b.strangers j perm (splitOf (b.right hlk)).toParent) := by
              exact_mod_cast Bag.strangers_union_le b j perm _ _
        _ ≤ p.γ * p.ε ^ j * capacity p k t (b.l + 1) +
            p.γ * p.ε ^ j * capacity p k t (b.l + 1) := by
              -- Each kick is bounded via kick_stranger_le
              have hkl : (b.left hlk).parent = b := Bag.left_parent_eq b hlk
              have hkr : (b.right hlk).parent = b := Bag.right_parent_eq b hlk
              have hll : 1 ≤ (b.left hlk).l := by show 1 ≤ b.l + 1; omega
              have hlr : 1 ≤ (b.right hlk).l := by show 1 ≤ b.l + 1; omega
              have hsl : (splitOf (b.left hlk)).toParent ⊆ pl.regs (b.left hlk) :=
                split_toParent_subset _ _
              have hsr : (splitOf (b.right hlk)).toParent ⊆ pl.regs (b.right hlk) :=
                split_toParent_subset _ _
              have hl := kick_stranger_le p k perm₀ t ih
                (b.left hlk) hll j hj _ hsl
              have hr := kick_stranger_le p k perm₀ t ih
                (b.right hlk) hlr j hj _ hsr
              rw [hkl] at hl; rw [hkr] at hr
              exact add_le_add hl hr
        _ = 2 * p.γ * p.ε ^ j * (p.A * cap) := by
              rw [capacity_succ]; ring
    · rw [dif_neg hlk, Bag.strangers_empty]; simp only [Nat.cast_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) p.hγ_pos.le) (pow_nonneg p.hε_pos.le _))
        (mul_nonneg hA_pos.le hcap_nn)
  -- Bound on fromParent
  have hfp_root : b.l = 0 → (b.strangers j perm (splitOf b).toParent : ℚ) = 0 := by
    intro hl0
    have hx0 : b.x = 0 := by have := b.hx; rw [hl0] at this; omega
    have hb_root : b = Bag.root k := Bag.ext hl0 hx0
    have hempty : (splitOf b).toParent = ∅ := by
      rw [hb_root]
      exact root_toParent_empty p k (by omega) t
    rw [hempty, Bag.strangers_empty]; simp
  -- Case split: j ≥ 2 or j = 1
  by_cases hj2 : 2 ≤ j
  · -- Case j ≥ 2: use stranger_gt1_arith
    -- fromParent bound
    have hfp : (b.strangers j perm
        (if b.l = 0 then (splitOf b).toParent
         else if b.x % 2 = 0 then (splitOf b.parent).toLeft
         else (splitOf b.parent).toRight) : ℚ) ≤
        p.γ * p.ε ^ (j - 1) * (cap / p.A) := by
      by_cases hl0 : b.l = 0
      · rw [if_pos hl0, hfp_root hl0]
        exact mul_nonneg (mul_nonneg p.hγ_pos.le (pow_nonneg p.hε_pos.le _))
          (div_nonneg hcap_nn hA_pos.le)
      · rw [if_neg hl0]
        have hl1 : 1 ≤ b.l := by omega
        -- cap/A = capacity at parent level
        have hcap_parent : cap / p.A = capacity p k t (b.l - 1) := by
          rw [hcap_def]
          have : capacity p k t b.l = p.A * capacity p k t (b.l - 1) := by
            conv_lhs => rw [show b.l = (b.l - 1) + 1 from by omega]
            exact capacity_succ p k t (b.l - 1)
          field_simp [show p.A ≠ 0 from by linarith]; linarith
        rw [hcap_parent]
        by_cases he : b.x % 2 = 0
        · rw [if_pos he]
          exact parent_stranger_j2_le p k perm₀ hperm t ih b hl1 j hj2 _
            Finset.subset_union_left
        · rw [if_neg he]
          exact parent_stranger_j2_le p k perm₀ hperm t ih b hl1 j hj2 _
            Finset.subset_union_right
    -- Combine kick + parent via stranger_gt1_arith
    calc (b.strangers j perm (stageRegs splitOf b) : ℚ)
        ≤ ↑(b.strangers j perm
            (if h : b.l < k then
              (splitOf (b.left h)).toParent ∪ (splitOf (b.right h)).toParent
            else ∅)) +
          ↑(b.strangers j perm
            (if b.l = 0 then (splitOf b).toParent
             else if b.x % 2 = 0 then (splitOf b.parent).toLeft
             else (splitOf b.parent).toRight)) := by
            simp only [stageRegs]
            exact_mod_cast Bag.strangers_union_le b j perm _ _
      _ ≤ 2 * p.γ * p.ε ^ j * (p.A * cap) +
          p.γ * p.ε ^ (j - 1) * (cap / p.A) := add_le_add hfc hfp
      _ ≤ p.γ * p.ε ^ (j - 1) * (p.ν * cap) :=
          stranger_gt1_arith hcap_nn hj2
  · -- Case j = 1 (since hj : 1 ≤ j and ¬(2 ≤ j))
    have hj1 : j = 1 := by omega
    subst hj1
    -- fromParent bound for j = 1
    have hfp : (b.strangers 1 perm
        (if b.l = 0 then (splitOf b).toParent
         else if b.x % 2 = 0 then (splitOf b.parent).toLeft
         else (splitOf b.parent).toRight) : ℚ) ≤
        (p.ε * p.γ / p.A + p.ε / (2 * p.A)
         + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
         + 1 / (8 * p.A ^ 3 - 2 * p.A)
         + p.γ / p.A
         + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by
      by_cases hl0 : b.l = 0
      · rw [if_pos hl0, hfp_root hl0]
        apply mul_nonneg _ hcap_nn
        have hε_pos := p.hε_pos
        have hγ_pos := p.hγ_pos
        have h_denom1 : (0 : ℚ) < 1 - (2 * p.ε * p.A) ^ 2 := by linarith [p.h2εA]
        have hA2 : (1 : ℚ) ≤ p.A ^ 2 := by nlinarith [p.hA]
        have h_denom2 : (0 : ℚ) < 8 * p.A ^ 3 - 2 * p.A := by nlinarith
        have h1 : (0 : ℚ) ≤ p.ε * p.γ / p.A := by positivity
        have h2 : (0 : ℚ) ≤ p.ε / (2 * p.A) := by positivity
        have h3 : (0 : ℚ) ≤ 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) := by positivity
        have h4 : (0 : ℚ) ≤ 1 / (8 * p.A ^ 3 - 2 * p.A) := by positivity
        have h5 : (0 : ℚ) ≤ p.γ / p.A := by positivity
        linarith
      · rw [if_neg hl0]
        have hl1 : 1 ≤ b.l := by omega
        by_cases he : b.x % 2 = 0
        · rw [if_pos he]
          exact parent_stranger_eq1_le p k hk perm₀ hperm t ht ih b hl1 _
            (by dsimp only; rw [if_pos he])
        · rw [if_neg he]
          exact parent_stranger_eq1_le p k hk perm₀ hperm t ht ih b hl1 _
            (by dsimp only; rw [if_neg he])
    -- Combine kick + parent via stranger_eq1_arith
    calc (b.strangers 1 perm (stageRegs splitOf b) : ℚ)
        ≤ ↑(b.strangers 1 perm
            (if h : b.l < k then
              (splitOf (b.left h)).toParent ∪ (splitOf (b.right h)).toParent
            else ∅)) +
          ↑(b.strangers 1 perm
            (if b.l = 0 then (splitOf b).toParent
             else if b.x % 2 = 0 then (splitOf b.parent).toLeft
             else (splitOf b.parent).toRight)) := by
            simp only [stageRegs]
            exact_mod_cast Bag.strangers_union_le b 1 perm _ _
      _ ≤ 2 * p.γ * p.ε * (p.A * cap) +
          (p.ε * p.γ / p.A + p.ε / (2 * p.A)
           + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
           + 1 / (8 * p.A ^ 3 - 2 * p.A)
           + p.γ / p.A
           + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by
            have hfc1 : (b.strangers 1 perm
                (if h : b.l < k then
                  (splitOf (b.left h)).toParent ∪ (splitOf (b.right h)).toParent
                else ∅) : ℚ) ≤ 2 * p.γ * p.ε * (p.A * cap) := by
              have := @hfc; simp only [pow_one] at this; exact this
            exact add_le_add hfc1 hfp
      _ ≤ p.γ * (p.ν * cap) := stranger_eq1_arith hcap_nn
      _ = p.γ * p.ε ^ (1 - 1) * (p.ν * cap) := by simp

/-! **Main Theorem** -/

/-- Stranger bound: at every stage t, the number of j-strangers in each bag
    is bounded by `γ · ε^(j-1) · capacity(p, k, t, l)`.

    Seiferas (2009), Section 5. Proved by induction on t (stage number).

    All parameter constraints are fields of `Params`. The capacity condition
    follows from `p.hC_bound` + `10 ≤ k` via `numStages_hcap_cond`. -/
theorem stranger_bound (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ht : t ≤ numStages p k) :
    let perm := (stages p k t).net.exec perm₀
    ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j perm
        ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l := by
  induction t with
  | zero =>
    exact stranger_bound_zero p k (by omega) perm₀
  | succ t ih =>
    exact stranger_bound_succ p k hk perm₀ hperm t (by omega)
      (ih (by omega))

end


