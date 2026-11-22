-- Prove2me | Definitions.Def_GirvingAKS_Bags_Sizes
-- name    : GirvingAKS_Bags_Sizes
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:00:20.105409+00:00
-- url     : https://prove2.me/theorems/d9fd4216-543c-4a11-bc33-f4515db9a0b0
-- title:
--   AKS sorting networks (Seiferas port) — Bag Size Analysis
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Sizes.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Pure arithmetic characterization of bag sizes across stages. Since `fringe` depends only on level (not horizontal index `x`), all bags at the same level have the same cardinality after each stage. This file defines that cardinality as a recurrence and proves it matches the actual `Placement` evolution.
--
--   Key definitions:
--
--   - `splitParentCard`, `splitChildCard`: split part cardinalities
--   - `rebagCard`: new bag cardinality after one rebag step
--   - `bagCard`: bag size as a function of level and stage number
--
--   Key theorem: `bagCard_eq_card` — bag sizes match the recurrence.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Sizes.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Network
import Definitions.Def_GirvingAKS_Bags_SplitCard

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Sizes.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bag Size Analysis

  Pure arithmetic characterization of bag sizes across stages.
  Since `fringe` depends only on level (not horizontal index `x`),
  all bags at the same level have the same cardinality after each stage.
  This file defines that cardinality as a recurrence and proves it
  matches the actual `Placement` evolution.

  Key definitions:
  - `splitParentCard`, `splitChildCard`: split part cardinalities
  - `rebagCard`: new bag cardinality after one rebag step
  - `bagCard`: bag size as a function of level and stage number

  Key theorem: `bagCard_eq_card` — bag sizes match the recurrence.
-/


section


open Finset

variable {k : ℕ}

/-! **Split Cardinality Correspondence** -/

private theorem split_card_partition (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    regs.card = (split regs f).toParent.card + (split regs f).toLeft.card +
                (split regs f).toRight.card := by
  have hpart : regs = (split regs f).toParent ∪ (split regs f).toLeft ∪
               (split regs f).toRight := by
    ext i; constructor
    · intro hi; rcases split_covers regs f hi with hp | hl | hr
      · exact mem_union_left _ (mem_union_left _ hp)
      · exact mem_union_left _ (mem_union_right _ hl)
      · exact mem_union_right _ hr
    · intro hi; rcases mem_union.mp hi with hpl | hr
      · rcases mem_union.mp hpl with hp | hl
        · exact split_toParent_subset regs f hp
        · exact split_toLeft_subset regs f hl
      · exact split_toRight_subset regs f hr
  conv_lhs => rw [hpart]
  have h1 : Disjoint ((split regs f).toParent ∪ (split regs f).toLeft) (split regs f).toRight :=
    disjoint_union_left.mpr ⟨split_toParent_toRight_disjoint regs f,
                              split_toLeft_toRight_disjoint regs f⟩
  rw [card_union_of_disjoint h1,
      card_union_of_disjoint (split_toParent_toLeft_disjoint regs f)]

private theorem card_filter_interval (s a b : ℕ) (hab : a ≤ b) (hbs : b ≤ s) :
    (univ.filter (fun j : Fin s ↦ a ≤ j.val ∧ j.val < b)).card = b - a := by
  by_cases hba : a = b
  · subst hba
    have : (univ.filter (fun j : Fin s ↦ a ≤ j.val ∧ j.val < a)) = ∅ := by
      rw [filter_eq_empty_iff]; intro j _; omega
    simp [this]
  · convert_to (Finset.map ⟨fun i : Fin (b - a) ↦ (⟨a + i.val, by omega⟩ : Fin s),
        fun i₁ i₂ heq ↦ by simp only [Fin.mk.injEq] at heq; exact Fin.ext (by omega)⟩
        univ).card = b - a
    · congr 1; ext ⟨j, hj⟩; constructor
      · intro hmem
        simp only [mem_filter, mem_univ, true_and] at hmem
        exact Finset.mem_map.mpr ⟨⟨j - a, by omega⟩, mem_univ _,
          Fin.ext (show a + (j - a) = j by omega)⟩
      · intro hmem
        obtain ⟨⟨i, hi⟩, -, heq⟩ := Finset.mem_map.mp hmem
        have heq' : a + i = j := congrArg Fin.val heq
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨by omega, by omega⟩
    · rw [card_map, card_univ, Fintype.card_fin]

/-- The `toLeft` part of `split` has `splitChildCard` elements. -/
theorem split_toLeft_card (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toLeft.card = splitChildCard regs.card f := by
  simp only [split, splitChildCard]
  rw [card_image_of_injective _ (regs.orderEmbOfFin rfl).injective]
  set s := regs.card; set h := s / 2 - f
  by_cases hs : h = 0
  · convert_to (∅ : Finset (Fin s)).card = h
    · congr 1; rw [filter_eq_empty_iff]; intro j _; omega
    · simp [hs]
  · have := card_filter_interval s f (f + h) (by omega) (by omega); omega

/-- The `toRight` part of `split` has `splitChildCard` elements. -/
theorem split_toRight_card (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toRight.card = splitChildCard regs.card f := by
  simp only [split, splitChildCard]
  rw [card_image_of_injective _ (regs.orderEmbOfFin rfl).injective]
  set s := regs.card; set h := s / 2 - f
  by_cases hs : h = 0
  · convert_to (∅ : Finset (Fin s)).card = h
    · congr 1; rw [filter_eq_empty_iff]; intro j _; omega
    · simp [hs]
  · have := card_filter_interval s (f + h) (f + 2 * h) (by omega) (by omega); omega

/-- The `toParent` part of `split` has `splitParentCard` elements. -/
theorem split_toParent_card (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toParent.card = splitParentCard regs.card f := by
  have hp := split_card_partition regs f
  rw [split_toLeft_card, split_toRight_card] at hp
  have := splitParentCard_add_two_childCard regs.card f
  omega

/-! **Rebag Cardinality** -/

/-- New bag size at level `l` after one rebag step, given the current
    bag size `sz l` and fringe `f l` at each level.

    Parallels the `rebag` definition in `Network.lean`:
    - `fromChildren`: two children (level `l+1`) each contribute their
      `splitParentCard` items (when `l + 1 ≤ k`)
    - `fromParent`:
      - Root (`l = 0`): keeps its own `splitParentCard` items
      - Non-root: receives one `splitChildCard` from parent (level `l-1`) -/
def rebagCard (k : ℕ) (sz : ℕ → ℕ) (f : ℕ → ℕ) (l : ℕ) : ℕ :=
  let fromChildren :=
    if l + 1 ≤ k then 2 * splitParentCard (sz (l + 1)) (f (l + 1))
    else 0
  let fromParent :=
    if l = 0 then splitParentCard (sz 0) (f 0)
    else splitChildCard (sz (l - 1)) (f (l - 1))
  fromChildren + fromParent

/-! **Initial Placement Properties** -/

theorem start_root_card :
    ((start k).regs (Bag.root k)).card = 2 ^ k := by
  simp [start, Bag.root]

theorem start_nonroot_card (b : Bag k) (hb : ¬(b.l = 0 ∧ b.x = 0)) :
    ((start k).regs b).card = 0 := by
  simp [start, hb]

/-! **Bag Size Recurrence** -/

/-- Number of registers in each bag at level `l` after `t` stages.
    - Stage 0: `2^k` at root (level 0), `0` elsewhere
    - Stage `t+1`: determined by `rebagCard` applied to stage-`t` sizes -/
def bagCard (p : Params) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 2 ^ k
  | 0, _ + 1 => 0
  | t + 1, l =>
    let sz l' := bagCard p k t l'
    let f l' := fringe p k t l' (sz l')
    rebagCard k sz f l

/-! **Size Invariant** -/

/-- After `t` stages, every valid bag at level `l` has exactly `bagCard p k t l`
    registers. Since `fringe` depends only on level, all bags at the same
    level evolve identically regardless of their horizontal index `x`.
    Restricted to valid bags (`b.x < 2 ^ b.l`) since phantom bags always have 0 elements. -/
theorem bagCard_eq_card (p : Params) (k : ℕ) :
    ∀ t (b : Bag k),
      ((stages p k t).value.regs b).card = bagCard p k t b.l := by
  intro t; induction t with
  | zero =>
    intro b
    simp only [stages, Build.value_pure]
    rcases b with ⟨l, x, hl, hx⟩
    cases l with
    | zero =>
      have : x = 0 := by omega
      subst this; simp [start, bagCard]
    | succ l =>
      simp only [bagCard, start]
      rw [if_neg (by omega : ¬(l + 1 = 0 ∧ x = 0))]
      exact Finset.card_empty
  | succ t ih =>
    intro b
    -- Unwind stages/stage to expose stageRegs
    have hregs : (stages p k (t + 1)).value.regs b =
        let pl := (stages p k t).value
        stageRegs (fun c ↦ split (pl.regs c) (fringe p k t c.l (pl.regs c).card)) b := by
      show (do let pl ← stages p k t; stage p pl t).value.regs b = _
      simp only [Build.value_bind]
      show (stage p (stages p k t).value t).value.regs b = _
      unfold stage separateAndSplit separate
      simp only [Build.value_bind, Build.value_pure]
    rw [hregs]
    set pl := (stages p k t).value with hpl_def
    let splitOf := fun c : Bag k ↦ split (pl.regs c) (fringe p k t c.l (pl.regs c).card)
    -- IH: card = bagCard for each contributing bag
    have ihL : ∀ h : b.l < k, (pl.regs (b.left h)).card = bagCard p k t (b.l + 1) :=
      fun h ↦ ih (b.left h)
    have ihR : ∀ h : b.l < k, (pl.regs (b.right h)).card = bagCard p k t (b.l + 1) :=
      fun h ↦ ih (b.right h)
    have ihP : b.l ≠ 0 → (pl.regs b.parent).card = bagCard p k t (b.l - 1) :=
      fun h0 ↦ ih b.parent
    have ihS : (pl.regs b).card = bagCard p k t b.l := ih b
    -- Abbreviations for .l projections
    have hLl : ∀ h : b.l < k, (b.left h).l = b.l + 1 := fun _ ↦ rfl
    have hRl : ∀ h : b.l < k, (b.right h).l = b.l + 1 := fun _ ↦ rfl
    have hPl : b.parent.l = b.l - 1 := rfl
    -- Disjointness helper: split parts from different bags are disjoint
    have sub_p : ∀ c : Bag k, (splitOf c).toParent ⊆ pl.regs c := fun c ↦
      split_toParent_subset _ _
    have sub_l : ∀ c : Bag k, (splitOf c).toLeft ⊆ pl.regs c := fun c ↦
      split_toLeft_subset _ _
    have sub_r : ∀ c : Bag k, (splitOf c).toRight ⊆ pl.regs c := fun c ↦
      split_toRight_subset _ _
    -- Case split on structure
    show (stageRegs splitOf b).card = bagCard p k (t + 1) b.l
    simp only [stageRegs, bagCard, rebagCard]
    by_cases hk : b.l < k
    · -- Children exist
      rw [dif_pos hk]
      have d_lr : Disjoint (splitOf (b.left hk)).toParent (splitOf (b.right hk)).toParent :=
        Disjoint.mono (sub_p _) (sub_p _)
          (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.right]))
      by_cases h0 : b.l = 0
      · -- Root with children
        rw [if_pos h0, if_pos (show b.l + 1 ≤ k from by omega), if_pos h0]
        have d_cp : Disjoint ((splitOf (b.left hk)).toParent ∪ (splitOf (b.right hk)).toParent)
                             ((splitOf b).toParent) :=
          disjoint_union_left.mpr
            ⟨Disjoint.mono (sub_p _) (sub_p _)
               (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left])),
             Disjoint.mono (sub_p _) (sub_p _)
               (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.right]))⟩
        rw [card_union_of_disjoint d_cp, card_union_of_disjoint d_lr,
            split_toParent_card, split_toParent_card, split_toParent_card,
            ihL hk, ihR hk, ihS]
        simp only [hLl, hRl, h0]; omega
      · -- Interior (children + parent)
        rw [if_neg h0, if_pos (show b.l + 1 ≤ k from by omega), if_neg h0]
        by_cases he : b.x % 2 = 0
        · -- Even: toLeft from parent
          rw [if_pos he]
          have d_cp : Disjoint ((splitOf (b.left hk)).toParent ∪ (splitOf (b.right hk)).toParent)
                               ((splitOf b.parent).toLeft) :=
            disjoint_union_left.mpr
              ⟨Disjoint.mono (sub_p _) (sub_l _)
                 (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.parent]; omega)),
               Disjoint.mono (sub_p _) (sub_l _)
                 (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.right, Bag.parent]; omega))⟩
          rw [card_union_of_disjoint d_cp, card_union_of_disjoint d_lr,
              split_toParent_card, split_toParent_card, split_toLeft_card,
              ihL hk, ihR hk, ihP h0]
          simp only [hLl, hRl, hPl]; omega
        · -- Odd: toRight from parent
          rw [if_neg he]
          have d_cp : Disjoint ((splitOf (b.left hk)).toParent ∪ (splitOf (b.right hk)).toParent)
                               ((splitOf b.parent).toRight) :=
            disjoint_union_left.mpr
              ⟨Disjoint.mono (sub_p _) (sub_r _)
                 (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.left, Bag.parent]; omega)),
               Disjoint.mono (sub_p _) (sub_r _)
                 (pl.disjoint _ _ (by simp [Bag.ext_iff, Bag.right, Bag.parent]; omega))⟩
          rw [card_union_of_disjoint d_cp, card_union_of_disjoint d_lr,
              split_toParent_card, split_toParent_card, split_toRight_card,
              ihL hk, ihR hk, ihP h0]
          simp only [hLl, hRl, hPl]; omega
    · -- No children (leaf or k=0 root)
      rw [dif_neg hk, if_neg (show ¬(b.l + 1 ≤ k) from by omega)]
      by_cases h0 : b.l = 0
      · -- k=0 root
        rw [if_pos h0, if_pos h0]
        simp only [empty_union]; rw [split_toParent_card, ihS, h0]; omega
      · -- Leaf
        rw [if_neg h0, if_neg h0]
        by_cases he : b.x % 2 = 0
        · rw [if_pos he]; simp only [empty_union]; rw [split_toLeft_card, ihP h0, hPl]; omega
        · rw [if_neg he]; simp only [empty_union]; rw [split_toRight_card, ihP h0, hPl]; omega

/-! **Size Properties** -/

/-- The root bag always has an even number of registers (for `k ≥ 1`).
    Root fringe is 0, so `splitParentCard` returns `s % 2`; children
    contribute `2 * X`. By induction the remainder is always 0. -/
theorem bagCard_root_even (p : Params) (k : ℕ) (hk : 1 ≤ k) (t : ℕ) :
    2 ∣ bagCard p k t 0 := by
  induction t with
  | zero => simp only [bagCard]; exact dvd_pow_self 2 (by omega)
  | succ t ih =>
    show 2 ∣ rebagCard k (bagCard p k t) (fun l' ↦ fringe p k t l' (bagCard p k t l')) 0
    simp only [rebagCard, show 0 + 1 ≤ k from by omega, ite_true, fringe, splitParentCard_zero]
    obtain ⟨m, hm⟩ := ih; rw [hm, Nat.mul_mod_right]; omega

/-- Bags at odd-parity levels are empty: if `(t + l) % 2 ≠ 0` then
    `bagCard p k t l = 0`. Requires `k ≥ 1` (for `k = 0` the single
    root bag persists at every stage).

    Proof: at stage `t+1`, a bag at level `l` receives from levels `l ± 1`,
    which have opposite parity and are therefore empty by IH. The root's
    self-contribution is `(bagCard p k t 0) % 2 = 0` by `bagCard_root_even`. -/
theorem bagCard_odd_eq_zero (p : Params) (k : ℕ) (hk : 1 ≤ k) :
    ∀ t l, (t + l) % 2 ≠ 0 → bagCard p k t l = 0 := by
  intro t; induction t with
  | zero =>
    intro l hodd
    match l with
    | 0 => simp at hodd
    | _ + 1 => simp [bagCard]
  | succ t ih =>
    intro l hodd
    show rebagCard k (bagCard p k t) (fun l' ↦ fringe p k t l' (bagCard p k t l')) l = 0
    simp only [rebagCard]
    have ih_succ : bagCard p k t (l + 1) = 0 := ih (l + 1) (by omega)
    have hfc : (if l + 1 ≤ k then 2 * splitParentCard (bagCard p k t (l + 1))
        (fringe p k t (l + 1) (bagCard p k t (l + 1))) else 0) = 0 := by
      split <;> simp [ih_succ, splitParentCard_zero_left]
    have hfp : (if l = 0 then splitParentCard (bagCard p k t 0)
          (fringe p k t 0 (bagCard p k t 0))
        else splitChildCard (bagCard p k t (l - 1))
          (fringe p k t (l - 1) (bagCard p k t (l - 1)))) = 0 := by
      by_cases h0 : l = 0
      · rw [if_pos h0]; simp only [fringe, ite_true, splitParentCard_zero]
        exact Nat.dvd_iff_mod_eq_zero.mp (bagCard_root_even p k hk t)
      · rw [if_neg h0, ih (l - 1) (by omega), splitChildCard_zero_left]
    rw [hfc, hfp]

/-- Bag sizes above level `k` are always 0. -/
theorem bagCard_above_k (p : Params) (k t l : ℕ) (hl : k < l) :
    bagCard p k t l = 0 := by
  suffices ∀ t l, k < l → bagCard p k t l = 0 from this t l hl
  intro t; induction t with
  | zero => intro l hl; match l, show l ≥ 1 from by omega with | l + 1, _ => simp [bagCard]
  | succ t ih =>
    intro l hl
    simp only [bagCard, rebagCard]
    have hfc : ¬(l + 1 ≤ k) := by omega
    have hl0 : ¬(l = 0) := by omega
    rw [if_neg hfc, if_neg hl0]
    simp only [splitChildCard]
    by_cases hmk : k < l - 1
    · rw [ih (l - 1) hmk]; simp
    · -- l - 1 = k
      have heq : l - 1 = k := by omega
      rw [heq]
      by_cases hk0 : k = 0
      · -- k = 0: fringe at level 0 = 0, need bagCard p 0 t 0 ≤ 1
        subst hk0; simp only [fringe, ite_true]
        have hle : bagCard p 0 t 0 ≤ 1 := by
          clear hl hl0 hfc hmk heq l
          induction t with
          | zero => simp [bagCard]
          | succ t iht =>
            simp only [bagCard, rebagCard, show ¬(0 + 1 ≤ 0) from by omega,
              ite_false, ite_true, fringe, splitParentCard]; omega
        omega
      · -- k ≥ 1: fringe at level k gives s/2
        simp only [fringe, show ¬(k = 0) from hk0, ite_false,
          show k ≤ k + 1 from by omega, ite_true]; omega

/-- Fringe at level `k` ensures `splitChildCard = 0` (leaf condition).
    Requires `k ≥ 1`; when `k = 0` the root IS the leaf and fringe = 0. -/
private theorem fringe_leaf_ge (p : Params) (k t s : ℕ) (hk : 1 ≤ k) :
    fringe p k t k s ≥ s / 2 := by
  simp only [fringe]
  rw [if_neg (by omega), if_pos (by omega)]

/-- Conservation: `rebagCard` preserves the weighted sum. -/
private theorem rebagCard_total_eq (k : ℕ) (sz f : ℕ → ℕ) (hleaf : f k ≥ sz k / 2) :
    ∑ l ∈ range (k + 1), 2 ^ l * rebagCard k sz f l =
    ∑ l ∈ range (k + 1), 2 ^ l * sz l := by
  let sP := fun l ↦ splitParentCard (sz l) (f l)
  let sC := fun l ↦ splitChildCard (sz l) (f l)
  have hpart : ∀ l, sP l + 2 * sC l = sz l := by
    intro l; simp only [sP, sC, splitParentCard, splitChildCard]; omega
  have hleaf' : sP k = sz k := by simp only [sP, splitParentCard]; omega
  -- Expand rebagCard and split sum
  simp_rw [show ∀ l, 2 ^ l * rebagCard k sz f l =
    2 ^ l * (if l + 1 ≤ k then 2 * sP (l + 1) else 0) +
    2 ^ l * (if l = 0 then sP 0 else sC (l - 1)) from
    fun l ↦ by show _ = _; unfold rebagCard; simp only [sP, sC]; ring]
  rw [sum_add_distrib]
  -- Children sum: peel off k term (= 0), simplify ifs
  rw [show ∑ l ∈ range (k + 1), 2 ^ l * (if l + 1 ≤ k then 2 * sP (l + 1) else 0) =
    ∑ l ∈ range k, 2 ^ (l + 1) * sP (l + 1) from by
    rw [sum_range_succ]
    simp only [show ¬(k + 1 ≤ k) from by omega, ite_false, Nat.mul_zero, add_zero]
    exact sum_congr rfl (fun l hl ↦ by
      rw [if_pos (by simp only [mem_range] at hl; omega)]; ring)]
  -- Parent sum: peel off 0 term, simplify ifs
  rw [show ∑ l ∈ range (k + 1), 2 ^ l * (if l = 0 then sP 0 else sC (l - 1)) =
    sP 0 + ∑ l ∈ range k, 2 ^ (l + 1) * sC l from by
    rw [sum_range_succ']
    simp only [ite_true, pow_zero, one_mul, show ∀ l : ℕ, ¬(l + 1 = 0) from by omega,
      ite_false, show ∀ l : ℕ, l + 1 - 1 = l from by omega]
    omega]
  -- Chain intermediate equalities
  have E5 : ∑ l ∈ range k, 2 ^ (l + 1) * sP (l + 1) + sP 0 =
    ∑ l ∈ range (k + 1), 2 ^ l * sP l := by
    have := sum_range_succ' (fun l ↦ 2 ^ l * sP l) k
    simp only [pow_zero, one_mul] at this; linarith
  have E6 := sum_range_succ (fun l ↦ 2 ^ l * sP l) k
  have E7 : ∑ l ∈ range k, 2 ^ l * sP l + ∑ l ∈ range k, 2 ^ (l + 1) * sC l =
    ∑ l ∈ range k, 2 ^ l * sz l := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun l _ ↦ by
      show 2 ^ l * sP l + 2 ^ (l + 1) * sC l = 2 ^ l * sz l
      have := hpart l
      calc _ = 2 ^ l * (sP l + 2 * sC l) := by ring
        _ = _ := by rw [this])
  have E8 := sum_range_succ (fun l ↦ 2 ^ l * sz l) k
  linarith [congrArg (2 ^ k * ·) hleaf']

/-- Total items across all bags equals `2^k` at every stage.
    At each level `l`, there are `2^l` bags, each with `bagCard p k t l` items. -/
theorem bagCard_total (p : Params) (k t : ℕ) :
    ∑ l ∈ Finset.range (k + 1), 2 ^ l * bagCard p k t l = 2 ^ k := by
  induction t with
  | zero =>
    rw [sum_range_succ']
    simp only [bagCard, pow_zero, one_mul, Nat.mul_zero, sum_const_zero, zero_add]
  | succ t ih =>
    have hunf : ∀ l, bagCard p k (t + 1) l =
      rebagCard k (bagCard p k t) (fun l' ↦ fringe p k t l' (bagCard p k t l')) l :=
      fun _ ↦ rfl
    simp_rw [hunf]
    by_cases hk : 1 ≤ k
    · exact (rebagCard_total_eq k _ _ (fringe_leaf_ge p k t _ hk)).trans ih
    · -- k = 0: single-element sum
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [Nat.zero_add, sum_range_one, pow_zero, one_mul] at ih ⊢
      simp only [rebagCard, show ¬(0 + 1 ≤ 0) from by omega, ite_false, ite_true,
        zero_add, fringe, splitParentCard]
      omega

/-- When all levels below `l` have `bagCard = 0`, `bagCard(t, l)` is even for `l < k`.

    From conservation: `∑ 2^{l'} · bagCard(l') = 2^k`. If the sum below `l` vanishes,
    then `bagCard(t, l) + ∑_{l'>l} 2^{l'-l} · bagCard(l') = 2^{k-l}`.
    Each term in the sum has factor `2^{l'-l} ≥ 2`, hence is even. And `2^{k-l}` is
    even since `l < k`. So `bagCard(t, l) = even - even = even`. -/
theorem bagCard_even_of_below_zero (p : Params) (k t l : ℕ) (hlk : l < k)
    (hbelow : ∀ l', l' < l → bagCard p k t l' = 0) :
    2 ∣ bagCard p k t l := by
  have htotal := bagCard_total p k t
  -- Split conservation sum at l
  have hsplit := (Finset.sum_range_add_sum_Ico
    (fun l' ↦ 2 ^ l' * bagCard p k t l') (by omega : l ≤ k + 1)).symm
  rw [htotal] at hsplit
  -- Zero out all levels below l
  have hsum_below : ∑ l' ∈ Finset.range l, 2 ^ l' * bagCard p k t l' = 0 :=
    Finset.sum_eq_zero (fun l' hl' ↦ by rw [hbelow l' (Finset.mem_range.mp hl')]; simp)
  rw [hsum_below, Nat.zero_add] at hsplit
  -- Isolate l from the Ico sum: ∑ Ico l (k+1) = 2^l * bc(l) + ∑ Ico (l+1) (k+1)
  rw [← Finset.sum_Ico_consecutive (fun l' ↦ 2 ^ l' * bagCard p k t l')
    (by omega : l ≤ l + 1) (by omega : l + 1 ≤ k + 1)] at hsplit
  rw [show Finset.Ico l (l + 1) = {l} from Nat.Ico_succ_singleton l,
    Finset.sum_singleton] at hsplit
  -- hsplit : 2^k = 2^l * bagCard(l) + ∑_{l'>l} 2^l' * bagCard(l')
  -- Show 2^{l+1} divides the sum above l
  have hS_div : 2 ^ (l + 1) ∣ ∑ l' ∈ Finset.Ico (l + 1) (k + 1),
      2 ^ l' * bagCard p k t l' :=
    Finset.dvd_sum (fun l' hl' ↦ dvd_mul_of_dvd_left
      (Nat.pow_dvd_pow 2 (Finset.mem_Ico.mp hl').1) _)
  -- 2^{l+1} divides 2^k since l+1 ≤ k
  have hpow_div : 2 ^ (l + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
  -- So 2^{l+1} divides 2^l * bagCard(l) = 2^k - S
  have hdiff_div : 2 ^ (l + 1) ∣ 2 ^ l * bagCard p k t l := by
    have h1 := hsplit
    rw [Nat.add_comm (2 ^ l * bagCard p k t l)] at h1
    rw [h1] at hpow_div
    exact (Nat.dvd_add_right hS_div).mp hpow_div
  -- 2^{l+1} = 2^l * 2, so 2 | bagCard(l)
  rw [show 2 ^ (l + 1) = 2 ^ l * 2 from by ring] at hdiff_div
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (by positivity))).mp hdiff_div

/-! **Structural Capacity Bound** -/

/-- Each bag has at most `bagSize k l = 2^k / 2^l` items.
    Follows from conservation: one term of a nonneg sum ≤ the total. -/
theorem bagCard_le_bagSize (p : Params) (k t l : ℕ) :
    bagCard p k t l ≤ bagSize k l := by
  by_cases hl : k < l
  · rw [bagCard_above_k p k t l hl]; exact Nat.zero_le _
  · push_neg at hl
    -- From bagCard_total: 2^l * bagCard p k t l ≤ 2^k
    have htotal := bagCard_total p k t
    have hterm : 2 ^ l * bagCard p k t l ≤
        ∑ l' ∈ Finset.range (k + 1), 2 ^ l' * bagCard p k t l' :=
      Finset.single_le_sum (f := fun l' ↦ 2 ^ l' * bagCard p k t l')
        (fun l' _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    rw [htotal] at hterm
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (by positivity))).mpr
      (by rw [Nat.mul_comm]; exact hterm)

/-! **Parametric Capacity** -/

/-- `capacity` at level 0 is `2^k · ν^t`. -/
theorem capacity_zero (p : Params) (k t : ℕ) :
    capacity p k t 0 = ↑(2 ^ k) * p.ν ^ t := by
  simp [capacity]

/-- `capacity` at the next level: `capacity p k t (l+1) = A · capacity p k t l`. -/
theorem capacity_succ (p : Params) (k t l : ℕ) :
    capacity p k t (l + 1) = p.A * capacity p k t l := by
  simp [capacity, pow_succ]; ring

/-- `capacity` is nonneg. -/
theorem capacity_nonneg (p : Params) (k t l : ℕ) :
    0 ≤ capacity p k t l := by
  unfold capacity
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg p.hν_pos.le _))
    (pow_nonneg (by linarith [p.hA]) _)

/-- `capacity p k (t+1) l = ν · capacity p k t l`. -/
theorem capacity_stage_succ (p : Params) (k t l : ℕ) :
    capacity p k (t + 1) l = p.ν * capacity p k t l := by
  simp [capacity, pow_succ]; ring

/-- `capacity` is monotone in level: `capacity p k t l ≤ capacity p k t (l + 1)`. -/
theorem capacity_mono_level (p : Params) (k t l : ℕ) :
    capacity p k t l ≤ capacity p k t (l + 1) := by
  rw [capacity_succ]
  exact le_mul_of_one_le_left (capacity_nonneg p k t l) p.hA.le

/-- `capacity` is monotone in level: `l ≤ l' → capacity p k t l ≤ capacity p k t l'`. -/
theorem capacity_mono_level_le (p : Params) (k t : ℕ) {l l' : ℕ} (h : l ≤ l') :
    capacity p k t l ≤ capacity p k t l' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih' => exact le_trans ih' (capacity_mono_level p k t _)

/-! **Large-cap slack lemmas (threshold A)** -/

/-- Non-root interior large-cap: `(4γA + 1/(2A))·cap + 2 ≤ ν·cap` when `A ≤ cap`.
    Slack = `(ν - 4γA - 1/(2A))·cap ≥ 2/A · A = 2`. -/
private theorem large_cap_interior_slack (p : Params) (cap : ℚ)
    (hcap : p.A ≤ cap) :
    (4 * p.γ * p.A + 1 / (2 * p.A)) * cap + 2 ≤ p.ν * cap := by
  have hA : (0 : ℚ) < p.A := by linarith [p.hA]
  have h1 : p.ν - 4 * p.γ * p.A - 1 / (2 * p.A) ≥ 2 / p.A := by
    have : 5 / (2 * p.A) - 1 / (2 * p.A) = 2 / p.A := by field_simp; ring
    linarith [p.hC3]
  have cap_nonneg : 0 ≤ cap := le_trans (by positivity : 0 ≤ p.A) hcap
  have slack_nonneg : 0 ≤ p.ν - 4 * p.γ * p.A - 1 / (2 * p.A) := by
    linarith [show 2 / p.A > 0 from by positivity]
  have h3 : 2 / p.A * p.A ≤ (p.ν - 4 * p.γ * p.A - 1 / (2 * p.A)) * cap :=
    mul_le_mul h1 hcap (by positivity) slack_nonneg
  have h4 : 2 / p.A * p.A = 2 := by field_simp
  linarith

/-- Leaf-children large-cap: `cap/(2A) + 4 ≤ ν·cap` when `A ≤ cap` and `γA² ≥ 1`.
    Slack = `(ν - 1/(2A))·cap ≥ (4γA + 2/A)·A = 4γA² + 2 ≥ 6 ≥ 4`. -/
private theorem large_cap_leaf_slack (p : Params) (cap : ℚ)
    (hcap : p.A ≤ cap) :
    1 / (2 * p.A) * cap + 4 ≤ p.ν * cap := by
  have hA : (0 : ℚ) < p.A := by linarith [p.hA]
  have h1 : p.ν - 1 / (2 * p.A) ≥ 4 * p.γ * p.A + 2 / p.A := by
    have : 5 / (2 * p.A) - 1 / (2 * p.A) = 2 / p.A := by field_simp; ring
    linarith [p.hC3]
  have cap_nonneg : 0 ≤ cap := le_trans (by positivity : 0 ≤ p.A) hcap
  have slack_nonneg : 0 ≤ p.ν - 1 / (2 * p.A) := by
    nlinarith [p.hγ_pos, p.hC3, show (0 : ℚ) < 2 / p.A from by positivity]
  have h3 : (4 * p.γ * p.A + 2 / p.A) * p.A ≤ (p.ν - 1 / (2 * p.A)) * cap :=
    mul_le_mul h1 hcap (by nlinarith [p.hγ_pos]) slack_nonneg
  have hA_ne : p.A ≠ 0 := ne_of_gt hA
  have h4 : 4 * p.γ * p.A ^ 2 + 2 ≤ p.ν * cap - 1 / (2 * p.A) * cap := by
    have : (4 * p.γ * p.A + 2 / p.A) * p.A = 4 * p.γ * p.A ^ 2 + 2 := by
      rw [add_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ hA_ne]; ring
    linarith
  nlinarith [p.hA2_le]

/-- Small-cap: `4γA·cap ≤ ν·cap`. Follows directly from `4γA ≤ ν` (from `hC3`). -/
private theorem small_cap_slack (p : Params) (cap : ℚ) (hcap : 0 ≤ cap) :
    4 * p.γ * p.A * cap ≤ p.ν * cap := by
  have hA : (0 : ℚ) < p.A := by linarith [p.hA]
  have : 4 * p.γ * p.A ≤ p.ν := by linarith [p.hC3, show (0 : ℚ) < 5 / (2 * p.A) from by positivity]
  exact mul_le_mul_of_nonneg_right this hcap

/-! **Parametric Capacity Bound** -/

/-- Bag cardinality bounded by parametric capacity under Seiferas constraints.

    Requires `A ≤ capacity(t, k-2)` so that near-leaf levels have enough
    capacity for the large-cap argument. Interior levels below the finish level
    use the small-cap argument (Seiferas 2009, Section 5, Clause 3, `b < A` case).

    Proof by induction on `t` (stage number):
    - Base `t=0`: `bagCard(0,0) = 2^k = cap(0,0)`, rest are 0.
    - Step `t→t+1`: for wrong-parity levels, `bagCard = 0` trivially.
      For right-parity levels, case split on `cap(t, l) ≥ A` vs `cap(t, l) < A`.
      **Large cap** (`A ≤ cap`): bound `rebagCard` using `splitParentCard ≤ 2f+1`;
      the `+2` rounding is absorbed since `(ν - 4γA - 1/(2A))·cap ≥ 2/A · A = 2`.
      **Small cap** (`cap < A`): ancestor levels have `cap < 1` hence `bagCard = 0`
      (by IH); alternating-level emptiness + conservation give even child bag sizes,
      eliminating the `+1` rounding: `splitParentCard(even, f) ≤ 2f`.
      Then `fromChildren ≤ 4γA·cap ≤ ν·cap` by `hC3`. Small cap can only occur at
      interior levels (`l + 3 ≤ k`) because `hfl` ensures `cap(k-2) ≥ A`. -/
theorem bagCard_le_capacity (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (hfl : p.A ≤ capacity p k t ((k - 2))) :
    ∀ l, (bagCard p k t l : ℚ) ≤ capacity p k t l := by
  induction t with
  | zero =>
    intro l; cases l with
    | zero => simp [bagCard, capacity]
    | succ l => simp [bagCard, capacity_nonneg]
  | succ t ih =>
    -- Derive IH: cap(t, k-2) ≥ A (from cap(t+1, k-2) ≥ A and ν < 1)
    have hfl_t : p.A ≤ capacity p k t ((k - 2)) := by
      by_contra h; push_neg at h
      have h1 := capacity_stage_succ p k t ((k - 2))
      have h2 : p.ν * capacity p k t ((k - 2)) < p.ν * p.A :=
        mul_lt_mul_of_pos_left h p.hν_pos
      have h3 : p.ν * p.A ≤ 1 * p.A :=
        mul_le_mul_of_nonneg_right p.hν_lt.le (by linarith [p.hA])
      linarith
    have ih := ih hfl_t
    have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
    -- Abbreviations
    let sz l' := bagCard p k t l'
    let f l' := fringe p k t l' (sz l')
    let cap l' := capacity p k t l'
    intro l
    show (bagCard p k (t + 1) l : ℚ) ≤ capacity p k (t + 1) l
    rw [capacity_stage_succ]
    -- Wrong-parity level: bagCard = 0
    by_cases hpar : (t + 1 + l) % 2 ≠ 0
    · rw [show bagCard p k (t + 1) l = 0 from bagCard_odd_eq_zero p k (by omega) _ _ hpar]
      simp; exact mul_nonneg p.hν_pos.le (capacity_nonneg p k t l)
    · push_neg at hpar
      -- Level l wrong parity at t
      have hl_empty : bagCard p k t l = 0 :=
        bagCard_odd_eq_zero p k (by omega) t l (by omega)
      -- Handle l > k: bagCard = 0
      by_cases hlk : k < l
      · rw [bagCard_above_k p k (t + 1) l hlk]
        simp; exact mul_nonneg p.hν_pos.le (capacity_nonneg p k t l)
      · push_neg at hlk
        show (rebagCard k sz f l : ℚ) ≤ p.ν * cap l
        -- l = k: rebagCard = 0 (leaf parent gives splitChildCard = 0)
        by_cases hlk' : l = k
        · simp only [rebagCard, show ¬(l + 1 ≤ k) from by omega,
            show l ≠ 0 from by omega, ite_false]
          have : f (l - 1) ≥ sz (l - 1) / 2 := by
            show fringe p k t (l - 1) _ ≥ _
            simp only [fringe, show ¬(l - 1 = 0) from by omega,
              show k ≤ (l - 1) + 1 from by omega, ite_true, ite_false]
            omega
          rw [splitChildCard_ge _ _ this]; simp
          exact mul_nonneg p.hν_pos.le (capacity_nonneg p k t l)
        · -- l ≤ k-1: children exist
          have hlk'' : l + 1 ≤ k := by omega
          -- fromParent bound (for l ≥ 1)
          have hfp_bound : ∀ hl1 : 1 ≤ l,
              (splitChildCard (sz (l - 1)) (f (l - 1)) : ℚ) ≤ cap l / (2 * p.A) := by
            intro hl1
            have hcap_eq : cap l = p.A * cap (l - 1) := by
              show capacity p k t l = p.A * capacity p k t (l - 1)
              conv_lhs => rw [show l = (l - 1) + 1 from by omega]
              exact capacity_succ p k t (l - 1)
            calc (splitChildCard (sz (l - 1)) (f (l - 1)) : ℚ)
                ≤ (sz (l - 1) : ℚ) / 2 := splitChildCard_le_half_cast _ _
              _ ≤ cap (l - 1) / 2 := by
                  exact div_le_div_of_nonneg_right (ih (l - 1)) (by positivity)
              _ = cap l / (2 * p.A) := by
                  rw [hcap_eq]; field_simp
          -- Case split on capacity: A ≤ cap(l) vs cap(l) < A
          by_cases hcap_A : p.A ≤ cap l
          · /-  LARGE CAP: A ≤ cap(l). -/
            by_cases hl0 : l = 0
            · -- Root large cap
              subst hl0
              have hf0 : f 0 = 0 := by show fringe p k t 0 _ = _; simp [fringe]
              suffices h : (rebagCard k sz f 0 : ℚ) ≤ 4 * p.γ * p.A * cap 0 + 2 by
                have hle : 4 * p.γ * p.A * cap 0 + 2 ≤
                    (4 * p.γ * p.A + 1 / (2 * p.A)) * cap 0 + 2 := by
                  have : 0 ≤ 1 / (2 * p.A) * cap 0 :=
                    mul_nonneg (by positivity) (capacity_nonneg p k t 0)
                  nlinarith
                exact le_trans h (le_trans hle (large_cap_interior_slack p (cap 0) hcap_A))
              simp only [rebagCard, hlk'', ite_true, hf0, splitParentCard_zero]
              have hroot_even := bagCard_root_even p k (by omega) t
              rw [show sz 0 % 2 = 0 from Nat.dvd_iff_mod_eq_zero.mp hroot_even]
              have hf1 : f 1 = ⌊p.γ * capacity p k t 1⌋₊ := by
                show fringe p k t 1 _ = _
                simp only [fringe, show ¬((1 : ℕ) = 0) from by omega,
                  show ¬(k ≤ 1 + 1) from by omega, ite_false]
              rw [hf1]; push_cast
              have h1 := splitParentCard_le_cast (sz 1) (⌊p.γ * capacity p k t 1⌋₊)
              have h2 : (⌊p.γ * capacity p k t 1⌋₊ : ℚ) ≤ p.γ * capacity p k t 1 :=
                Nat.floor_le (mul_nonneg p.hγ_pos.le (capacity_nonneg p k t 1))
              have h3 : p.γ * capacity p k t 1 = p.γ * p.A * cap 0 := by
                rw [capacity_succ]; ring
              push_cast at h1; nlinarith
            · -- Non-root large cap
              have hl1 : 1 ≤ l := by omega
              have hfp := hfp_bound hl1
              by_cases hic : l + 3 ≤ k
              · -- Interior children
                suffices h : (rebagCard k sz f l : ℚ) ≤
                    (4 * p.γ * p.A + 1 / (2 * p.A)) * cap l + 2 from
                  le_trans h (large_cap_interior_slack p (cap l) hcap_A)
                simp only [rebagCard, hlk'', ite_true, show ¬(l = 0) from hl0, ite_false]
                push_cast
                have hf_eq : f (l + 1) = ⌊p.γ * capacity p k t (l + 1)⌋₊ := by
                  show fringe p k t (l + 1) _ = _
                  simp only [fringe, show ¬(l + 1 = 0) from by omega,
                    show ¬(k ≤ l + 1 + 1) from by omega, ite_false]
                have hfl' : (f (l + 1) : ℚ) ≤ p.γ * capacity p k t (l + 1) := by
                  rw [hf_eq]
                  exact Nat.floor_le (mul_nonneg p.hγ_pos.le (capacity_nonneg p k t (l + 1)))
                have h1 : (splitParentCard (sz (l + 1)) (f (l + 1)) : ℚ) ≤
                    2 * (p.γ * capacity p k t (l + 1)) + 1 := by linarith [splitParentCard_le_cast (sz (l + 1)) (f (l + 1))]
                have h3 : capacity p k t (l + 1) = p.A * cap l :=
                  capacity_succ p k t l
                rw [h3] at h1
                have h_eq : cap l / (2 * p.A) = 1 / (2 * p.A) * cap l := by ring
                nlinarith
              · -- Leaf children
                suffices h : (rebagCard k sz f l : ℚ) ≤
                    1 / (2 * p.A) * cap l + 4 from
                  le_trans h (large_cap_leaf_slack p (cap l) hcap_A)
                simp only [rebagCard, hlk'', ite_true, show ¬(l = 0) from hl0, ite_false]
                push_cast
                have hle : sz (l + 1) ≤ bagSize k (l + 1) :=
                  bagCard_le_bagSize p k t (l + 1)
                have hbs : bagSize k (l + 1) ≤ 2 := by
                  simp only [bagSize]
                  have hkle : k ≤ l + 2 := by omega
                  calc 2 ^ k / 2 ^ (l + 1)
                      ≤ 2 ^ (l + 2) / 2 ^ (l + 1) :=
                        Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hkle)
                    _ = 2 := by
                        rw [show l + 2 = (l + 1) + 1 from by omega, pow_succ]
                        exact Nat.mul_div_cancel_left _ (by positivity)
                have hsz_le : (sz (l + 1) : ℚ) ≤ 2 := by exact_mod_cast le_trans hle hbs
                have hf_eq : f (l + 1) = sz (l + 1) / 2 := by
                  show fringe p k t (l + 1) _ = _
                  simp only [fringe, show ¬(l + 1 = 0) from by omega,
                    show k ≤ l + 1 + 1 from by omega, ite_true, ite_false]
                have hfc : (splitParentCard (sz (l + 1)) (f (l + 1)) : ℚ) ≤ 2 := by
                  rw [hf_eq, splitParentCard_ge _ _ (le_refl _)]
                  exact_mod_cast le_trans hle hbs
                have h_eq : cap l / (2 * p.A) = 1 / (2 * p.A) * cap l := by ring
                linarith
          · /-  SMALL CAP: cap(l) < A.
              Ancestors have cap < 1, so bagCard = 0. Children are even by
              conservation. No +1 rounding, so bound is 4γA·cap ≤ ν·cap.
              Small cap implies l ≤ k-3 (interior), because hfl gives
              cap(k-2) ≥ A, so cap(l) < A forces l < k-2. -/
            push_neg at hcap_A
            -- Small cap implies l < k-2, so l+3 ≤ k
            have hsmall_l : l + 3 ≤ k := by
              by_contra hle; push_neg at hle
              -- l ≥ k-2, so cap(l) ≥ cap(k-2) ≥ A
              have hfl_le : (k - 2) ≤ l := by omega
              have : cap ((k - 2)) ≤ cap l := by
                show capacity p k t ((k - 2)) ≤ capacity p k t l
                exact capacity_mono_level_le p k t hfl_le
              linarith
            -- All levels below l+1 at stage t are 0
            have hbelow : ∀ l', l' < l + 1 → bagCard p k t l' = 0 := by
              intro l' hl'
              by_cases hpar' : (t + l') % 2 ≠ 0
              · exact bagCard_odd_eq_zero p k (by omega) t l' hpar'
              · push_neg at hpar'
                -- l' has right parity at t, l' < l+1. Since l has wrong parity at t
                -- and l' has right: l' ≠ l, so l' ≤ l-1, so l' < l.
                have hl'_lt : l' < l := by omega
                -- cap(l') = cap(l) / A^(l-l') < A / A^(l-l') ≤ A/A = 1
                have hcap_l' : capacity p k t l' < 1 := by
                  -- cap(l'+1) ≤ cap(l) by monotonicity (l'+1 ≤ l)
                  have hmono_succ : capacity p k t (l' + 1) ≤ capacity p k t l :=
                    capacity_mono_level_le p k t hl'_lt
                  -- cap(l'+1) = A * cap(l')
                  rw [capacity_succ] at hmono_succ
                  -- A * cap(l') ≤ cap(l) < A, so cap(l') < 1
                  have : p.A * capacity p k t l' < p.A * 1 := by linarith
                  exact lt_of_mul_lt_mul_of_nonneg_left this (by linarith [p.hA])
                have h_ih := ih l'
                have : (bagCard p k t l' : ℚ) < 1 := lt_of_le_of_lt h_ih hcap_l'
                exact Nat.lt_one_iff.mp (by exact_mod_cast this)
            -- Children at l+1 are even (conservation + below-zero)
            have heven : 2 ∣ sz (l + 1) :=
              bagCard_even_of_below_zero p k t (l + 1) (by omega) hbelow
            -- Root and non-root share same structure: fromParent = 0
            by_cases hl0 : l = 0
            · -- Root small cap
              subst hl0
              suffices h : (rebagCard k sz f 0 : ℚ) ≤ 4 * p.γ * p.A * cap 0 from
                le_trans h (small_cap_slack p (cap 0) (capacity_nonneg p k t 0))
              have hf0 : f 0 = 0 := by show fringe p k t 0 _ = _; simp [fringe]
              have hsz0 : sz 0 = 0 := hl_empty
              have hf1 : f 1 = ⌊p.γ * capacity p k t 1⌋₊ := by
                show fringe p k t 1 _ = _
                simp only [fringe, show ¬((1 : ℕ) = 0) from by omega,
                  show ¬(k ≤ 1 + 1) from by omega, ite_false]
              have hreb : rebagCard k sz f 0 =
                  2 * splitParentCard (sz 1) ⌊p.γ * capacity p k t 1⌋₊ := by
                simp only [rebagCard, hlk'', ite_true, hf0, hsz0, hf1,
                  splitParentCard_zero, Nat.zero_mod, Nat.add_zero]
              rw [hreb]; push_cast
              have h1 : (splitParentCard (sz 1) (⌊p.γ * capacity p k t 1⌋₊) : ℚ) ≤
                  2 * ↑⌊p.γ * capacity p k t 1⌋₊ := by
                exact_mod_cast splitParentCard_le_two_f_of_even (sz 1)
                  (⌊p.γ * capacity p k t 1⌋₊) heven
              have h2 := Nat.floor_le (mul_nonneg p.hγ_pos.le (capacity_nonneg p k t 1))
              have h3 : p.γ * capacity p k t 1 = p.γ * p.A * cap 0 := by
                rw [capacity_succ]; ring
              nlinarith
            · -- Non-root small cap: fromParent = 0 (parent cap < 1 by IH)
              have hl1 : 1 ≤ l := by omega
              simp only [rebagCard, hlk'', ite_true, show ¬(l = 0) from hl0, ite_false]
              push_cast
              -- fromParent = splitChildCard(sz(l-1), f(l-1)). Parent level l-1 is
              -- non-empty at t but has cap < 1, so sz(l-1) = 0 → fromParent = 0.
              have hparent_zero : sz (l - 1) = 0 :=
                hbelow (l - 1) (by omega)
              have hfp_zero : (splitChildCard (sz (l - 1)) (f (l - 1)) : ℚ) = 0 := by
                rw [hparent_zero]; simp [splitChildCard]
              -- f(l+1) = ⌊γ·cap(l+1)⌋₊ (interior children)
              have hf_eq : f (l + 1) = ⌊p.γ * capacity p k t (l + 1)⌋₊ := by
                show fringe p k t (l + 1) _ = _
                simp only [fringe, show ¬(l + 1 = 0) from by omega,
                  show ¬(k ≤ l + 1 + 1) from by omega, ite_false]
              rw [hf_eq]
              have h1 : (splitParentCard (sz (l + 1)) (⌊p.γ * capacity p k t (l + 1)⌋₊) : ℚ) ≤
                  2 * ↑⌊p.γ * capacity p k t (l + 1)⌋₊ := by
                exact_mod_cast splitParentCard_le_two_f_of_even (sz (l + 1))
                  (⌊p.γ * capacity p k t (l + 1)⌋₊) heven
              have h2 := Nat.floor_le (mul_nonneg p.hγ_pos.le (capacity_nonneg p k t (l + 1)))
              have h3 : p.γ * capacity p k t (l + 1) = p.γ * p.A * cap l := by
                rw [capacity_succ]; ring
              push_cast at h1
              -- rebagCard ≤ 2·splitParentCard + 0 ≤ 2·2γA·cap = 4γA·cap ≤ ν·cap
              have hbd : 2 * (splitParentCard (sz (l + 1)) (⌊p.γ * capacity p k t (l + 1)⌋₊) : ℚ) +
                  (splitChildCard (sz (l - 1)) (f (l - 1)) : ℚ) ≤ 4 * p.γ * p.A * cap l := by
                rw [hfp_zero, add_zero]; nlinarith
              exact le_trans hbd (small_cap_slack p (cap l) (capacity_nonneg p k t l))

/-- Bridge: `t ≤ numStages` implies the convergence-level capacity bound needed by
    `bagCard_le_capacity`. At `numStages`, `cap(cl) ≥ ν/γ ≥ A` (from hC3).
    For `t ≤ numStages`, capacity is even larger. -/
theorem numStages_hfl (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (ht : t ≤ numStages p k) :
    p.A ≤ capacity p k t ((k - 2)) := by
  have hpos := numStages_pos p k hk
  have hpre := numStages_pre p k (numStages p k - 1) (by omega)
  -- cap(ns-1, cl) = cap(ns, cl) / ν
  have hcap_rel : capacity p k (numStages p k - 1) ((k - 2)) =
      capacity p k (numStages p k) ((k - 2)) / p.ν := by
    unfold capacity; rw [eq_div_iff (ne_of_gt p.hν_pos)]
    calc (2:ℚ) ^ k * p.ν ^ (numStages p k - 1) * p.A ^ (k - 2) * p.ν
        = (2:ℚ) ^ k * (p.ν ^ (numStages p k - 1) * p.ν) * p.A ^ (k - 2) := by ring
      _ = (2:ℚ) ^ k * p.ν ^ numStages p k * p.A ^ (k - 2) := by
          rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hpos]
  rw [hcap_rel] at hpre
  set cns := capacity p k (numStages p k) ((k - 2))
  -- 1 ≤ γ * (cns/ν) → ν/γ ≤ cns
  have hν_ne : p.ν ≠ 0 := ne_of_gt p.hν_pos
  have hνγ_le : p.ν / p.γ ≤ cns := by
    rw [div_le_iff₀ p.hγ_pos]
    have h := mul_le_mul_of_nonneg_left hpre (show (0:ℚ) ≤ p.ν by linarith [p.hν_pos])
    simp only [mul_one] at h
    have heq : p.ν * (p.γ * (cns / p.ν)) = cns * p.γ := by field_simp
    linarith
  -- A ≤ ν/γ from hC3: ν ≥ 4γA ≥ γA
  have hA_le_νγ : p.A ≤ p.ν / p.γ := by
    rw [le_div_iff₀ p.hγ_pos]
    have h5 := p.hC3; have hA : (0:ℚ) < p.A := by linarith [p.hA]
    have h6 : (0:ℚ) ≤ 5 / (2 * p.A) := div_nonneg (by norm_num) (by linarith)
    have h7 : p.A * p.γ ≤ 4 * p.γ * p.A := by nlinarith [p.hγ_pos]
    linarith
  exact le_trans hA_le_νγ (le_trans hνγ_le (numStages_cap_mono p k t _ ht))

end


