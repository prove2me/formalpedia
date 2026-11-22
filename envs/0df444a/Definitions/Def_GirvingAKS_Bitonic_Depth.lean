-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_Depth
-- name    : GirvingAKS_Bitonic_Depth
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:05.148482+00:00
-- url     : https://prove2.me/theorems/fe2b9f11-7bf5-4f9b-8f54-d88f584a2b5b
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort — Depth Bounds
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/Depth.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Fully proved depth bounds for Batcher's bitonic sorting network.
--
--   Main results:
--
--   - `bitonicCompareLayer_depth_le` : depth ≤ 1
--   - `bitonicCrossLayer_depth_le`   : depth ≤ 1
--   - `flip_depth_le`                : flipping preserves depth
--   - `bitonicMerge_depth_le`        : depth ≤ k
--   - `bitonicSort_depth_le`         : depth ≤ k²
--   - `bitonicSort_depth_clog`       : depth ≤ (Nat.clog 2 (2^k))²
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/Depth.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_Defs
import Definitions.Def_GirvingAKS_Sort_Depth

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/Depth.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort — Depth Bounds

  Fully proved depth bounds for Batcher's bitonic sorting network.

  Main results:
  - `bitonicCompareLayer_depth_le` : depth ≤ 1
  - `bitonicCrossLayer_depth_le`   : depth ≤ 1
  - `flip_depth_le`                : flipping preserves depth
  - `bitonicMerge_depth_le`        : depth ≤ k
  - `bitonicSort_depth_le`         : depth ≤ k²
  - `bitonicSort_depth_clog`       : depth ≤ (Nat.clog 2 (2^k))²
-/


section

/-! **Compare Layer is Parallel** -/

/-- The bitonic compare layer is a parallel layer: all comparators are pairwise
    non-overlapping. -/
theorem bitonicCompareLayer_isParallel (k : Nat) :
    IsParallelLayer (bitonicCompareLayer k).comparators := by
  simp only [bitonicCompareLayer, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange (2^k))
  intro i₁ i₂ hne
  unfold Comparator.overlaps; push_neg
  have h1 : i₁.val ≠ i₂.val := Fin.val_ne_of_ne hne
  exact ⟨by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega⟩

/-- The bitonic compare layer has depth ≤ 1. -/
theorem bitonicCompareLayer_depth_le (k : Nat) :
    (bitonicCompareLayer k).depth ≤ 1 := by
  apply depth_le_of_decomposition _ [(bitonicCompareLayer k).comparators]
  refine ⟨fun layer h ↦ ?_, by simp [List.flatten]⟩
  simp only [List.mem_singleton] at h; rw [h]
  exact bitonicCompareLayer_isParallel k

/-! **Cross Layer is Parallel** -/

/-- The bitonic cross layer is a parallel layer: all comparators are pairwise
    non-overlapping. -/
theorem bitonicCrossLayer_isParallel (k : Nat) :
    IsParallelLayer (bitonicCrossLayer k).comparators := by
  simp only [bitonicCrossLayer, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange (2^k))
  intro i₁ i₂ hne
  unfold Comparator.overlaps; push_neg
  have h1 : i₁.val ≠ i₂.val := Fin.val_ne_of_ne hne
  exact ⟨by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega⟩

/-- The bitonic cross layer has depth ≤ 1. -/
theorem bitonicCrossLayer_depth_le (k : Nat) :
    (bitonicCrossLayer k).depth ≤ 1 := by
  apply depth_le_of_decomposition _ [(bitonicCrossLayer k).comparators]
  refine ⟨fun layer h ↦ ?_, by simp [List.flatten]⟩
  simp only [List.mem_singleton] at h; rw [h]
  exact bitonicCrossLayer_isParallel k

/-! **Flip Preserves Depth** -/

/-- Processing flipped comparators maintains the running max.
    Invariant: `wt j.rev = wt₀ j` for all `j`. -/
lemma foldl_flip_eq {n : Nat} (cs : List (Comparator n))
    (wt₀ : Fin n → Nat) (wt : Fin n → Nat) (dm : Nat)
    (hwt : ∀ j : Fin n, wt j.rev = wt₀ j) :
    let flipped := cs.map fun c ↦
      ({ i := c.j.rev, j := c.i.rev, h := Fin.rev_lt_rev.mpr c.h } : Comparator n)
    (flipped.foldl depthStep (wt, dm)).2 = (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    set c' : Comparator n :=
      { i := c.j.rev, j := c.i.rev, h := Fin.rev_lt_rev.mpr c.h }
    -- Wire times at flipped positions
    have h_ci : wt c'.i = wt₀ c.j := hwt c.j
    have h_cj : wt c'.j = wt₀ c.i := hwt c.i
    -- Running max is equal (max is symmetric)
    have hdm_eq : (depthStep (wt, dm) c').2 = (depthStep (wt₀, dm) c).2 := by
      simp only [depthStep, h_ci, h_cj, Nat.max_comm (wt₀ c.j) (wt₀ c.i)]
    -- Wire-time correspondence preserved after one step
    have hwt_step : ∀ j : Fin n,
        (depthStep (wt, dm) c').1 j.rev = (depthStep (wt₀, dm) c).1 j := by
      intro j
      simp only [depthStep, Function.update_apply, h_ci, h_cj,
        Nat.max_comm (wt₀ c.j) (wt₀ c.i)]
      -- LHS checks j.rev vs c'.j (= c.i.rev), then j.rev vs c'.i (= c.j.rev)
      -- RHS checks j vs c.j, then j vs c.i
      -- j.rev = c.i.rev ↔ j = c.i, j.rev = c.j.rev ↔ j = c.j
      by_cases hji : j = c.i
      · -- j.rev = c'.j = c.i.rev: true
        have h1 : j.rev = c'.j := congr_arg Fin.rev hji
        rw [if_pos h1]
        -- RHS: j ≠ c.j (since c.i < c.j), j = c.i
        have h2 : ¬(j = c.j) := fun h ↦ (Fin.ne_of_lt c.h) (hji ▸ h)
        rw [if_neg h2, if_pos hji]
      · -- j.rev ≠ c'.j = c.i.rev
        have h1 : j.rev ≠ c'.j := fun h ↦ hji (Fin.rev_injective h)
        rw [if_neg h1]
        by_cases hjj : j = c.j
        · -- j.rev = c'.i = c.j.rev: true
          have h2 : j.rev = c'.i := congr_arg Fin.rev hjj
          rw [if_pos h2, if_pos hjj]
        · -- j.rev ≠ c'.i = c.j.rev
          have h2 : j.rev ≠ c'.i := fun h ↦ hjj (Fin.rev_injective h)
          rw [if_neg h2, if_neg hjj, if_neg hji, hwt j]
    -- Apply IH
    have step := ih (depthStep (wt₀, dm) c).1 (depthStep (wt, dm) c').1
      (depthStep (wt, dm) c').2 hwt_step
    simp only at step
    rw [Prod.mk.eta] at step
    rw [hdm_eq, Prod.mk.eta] at step
    exact step

/-- Flipping a network preserves its depth. -/
theorem flip_depth_le {n : Nat} (net : ComparatorNetwork n) :
    net.flip.depth ≤ net.depth := by
  simp only [ComparatorNetwork.depth, ComparatorNetwork.flip]
  have := foldl_flip_eq net.comparators (fun _ ↦ 0) (fun _ ↦ 0) 0
    (fun _ ↦ rfl)
  dsimp only at this; rw [this]

/-! **Shift Embedding Wire Range** -/

/-- Comparator wires in a shift-embedded network lie in `[offset, offset+m)`. -/
lemma shiftEmbed_wires_range {m : Nat} (net : ComparatorNetwork m)
    (n offset : Nat) (h : offset + m ≤ n)
    (c : Comparator n) (hc : c ∈ (net.shiftEmbed n offset h).comparators) :
    offset ≤ c.i.val ∧ c.i.val < offset + m ∧
    offset ≤ c.j.val ∧ c.j.val < offset + m := by
  simp only [ComparatorNetwork.shiftEmbed, List.mem_map] at hc
  obtain ⟨c₀, _, rfl⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · show offset ≤ offset + c₀.i.val; omega
  · show offset + c₀.i.val < offset + m; have := c₀.i.isLt; omega
  · show offset ≤ offset + c₀.j.val; omega
  · show offset + c₀.j.val < offset + m; have := c₀.j.isLt; omega

/-! **Wire-Disjoint Append** -/

/-- Two wire-disjoint networks can execute in parallel: the depth of their
    concatenation is at most the max of their individual depths. -/
lemma depth_append_wire_disjoint {n : Nat}
    (left right : ComparatorNetwork n) (d : Nat)
    (hd_left : left.depth ≤ d) (hd_right : right.depth ≤ d)
    (h_disj : ∀ c₁ ∈ left.comparators, ∀ c₂ ∈ right.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) :
    (⟨left.comparators ++ right.comparators⟩ : ComparatorNetwork n).depth ≤ d := by
  -- Express as flatMap over [true, false]
  have h_flat : left.comparators ++ right.comparators =
      [true, false].flatMap (fun b ↦ if b then left.comparators else right.comparators) := by
    simp [List.flatMap]
  rw [show (⟨left.comparators ++ right.comparators⟩ : ComparatorNetwork n) =
    ⟨[true, false].flatMap (fun b ↦ if b then left.comparators else right.comparators)⟩
    from ComparatorNetwork.ext h_flat]
  apply depth_flatMap_disjoint
  · intro b hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl <;> simpa
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩⟩
    · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb; simpa using h_disj
    · intro b hb; simp at hb

/-! **Merge Depth** -/

/-- Bitonic merge has depth ≤ k. -/
theorem bitonicMerge_depth_le : ∀ (k : Nat), (bitonicMerge k).depth ≤ k
  | 0 => by simp [bitonicMerge, depth_nil]
  | k + 1 => by
    unfold bitonicMerge
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    set layer := bitonicCompareLayer k
    set left := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    set right := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    -- depth(layer ++ (left ++ right)) ≤ depth(layer) + depth(left ++ right)
    have h_assoc : layer.comparators ++ left.comparators ++ right.comparators =
        layer.comparators ++ (left.comparators ++ right.comparators) :=
      List.append_assoc _ _ _
    calc (⟨layer.comparators ++ left.comparators ++ right.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth
        = (⟨layer.comparators ++ (left.comparators ++ right.comparators)⟩ :
            ComparatorNetwork (2^(k+1))).depth := by rw [h_assoc]
      _ ≤ layer.depth + (⟨left.comparators ++ right.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth :=
          depth_append ⟨layer.comparators⟩ ⟨left.comparators ++ right.comparators⟩
      _ ≤ 1 + k := by
          apply Nat.add_le_add (bitonicCompareLayer_depth_le k)
          exact depth_append_wire_disjoint left right k
            (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
            (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
            (fun c₁ hc₁ c₂ hc₂ ↦ by
              have hl := shiftEmbed_wires_range (bitonicMerge k) _ 0 h0 c₁ hc₁
              have hr := shiftEmbed_wires_range (bitonicMerge k) _ (2^k) h1 c₂ hc₂
              exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
                     by intro h; have := congr_arg Fin.val h; omega⟩,
                    ⟨by intro h; have := congr_arg Fin.val h; omega,
                     by intro h; have := congr_arg Fin.val h; omega⟩⟩)
      _ = k + 1 := by omega

/-! **Sort Depth** -/

/-- Bitonic sort has depth ≤ k². -/
theorem bitonicSort_depth_le : ∀ (k : Nat), (bitonicSort k).depth ≤ k ^ 2
  | 0 => by simp [bitonicSort, depth_nil]
  | k + 1 => by
    unfold bitonicSort
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    set sortLeft := (bitonicSort k).shiftEmbed (2^(k+1)) 0 h0
    set sortRight := (bitonicSort k).shiftEmbed (2^(k+1)) (2^k) h1
    set cross := bitonicCrossLayer k
    set mergeLeft := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    set mergeRight := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    -- Regroup: (S ++ R ++ X ++ ML ++ MR) = (S ++ R) ++ (X ++ (ML ++ MR))
    have h_assoc : sortLeft.comparators ++ sortRight.comparators ++
        cross.comparators ++ mergeLeft.comparators ++ mergeRight.comparators =
        (sortLeft.comparators ++ sortRight.comparators) ++
        (cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)) := by
      simp only [List.append_assoc]
    -- Wire disjointness helper for left/right at offsets 0 and 2^k
    have h_disj_sort : ∀ c₁ ∈ sortLeft.comparators, ∀ c₂ ∈ sortRight.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) :=
      fun c₁ hc₁ c₂ hc₂ ↦ by
        have hl := shiftEmbed_wires_range (bitonicSort k) _ 0 h0 c₁ hc₁
        have hr := shiftEmbed_wires_range (bitonicSort k) _ (2^k) h1 c₂ hc₂
        exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩,
              ⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩⟩
    have h_disj_merge : ∀ c₁ ∈ mergeLeft.comparators, ∀ c₂ ∈ mergeRight.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) :=
      fun c₁ hc₁ c₂ hc₂ ↦ by
        have hl := shiftEmbed_wires_range (bitonicMerge k) _ 0 h0 c₁ hc₁
        have hr := shiftEmbed_wires_range (bitonicMerge k) _ (2^k) h1 c₂ hc₂
        exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩,
              ⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩⟩
    calc (⟨sortLeft.comparators ++ sortRight.comparators ++
            cross.comparators ++ mergeLeft.comparators ++ mergeRight.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth
        = (⟨(sortLeft.comparators ++ sortRight.comparators) ++
            (cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators))⟩ :
            ComparatorNetwork (2^(k+1))).depth := by rw [h_assoc]
      _ ≤ (⟨sortLeft.comparators ++ sortRight.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth +
          (⟨cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)⟩ :
            ComparatorNetwork (2^(k+1))).depth :=
          depth_append _ _
      _ ≤ k ^ 2 + (1 + k) := by
          apply Nat.add_le_add
          · exact depth_append_wire_disjoint sortLeft sortRight (k ^ 2)
              (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicSort_depth_le k))
              (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicSort_depth_le k))
              h_disj_sort
          · calc (⟨cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)⟩ :
                    ComparatorNetwork (2^(k+1))).depth
                ≤ cross.depth + (⟨mergeLeft.comparators ++ mergeRight.comparators⟩ :
                    ComparatorNetwork (2^(k+1))).depth :=
                  depth_append _ _
              _ ≤ 1 + k := Nat.add_le_add (bitonicCrossLayer_depth_le k)
                  (depth_append_wire_disjoint mergeLeft mergeRight k
                    (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
                    (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
                    h_disj_merge)
      _ ≤ (k + 1) ^ 2 := by ring_nf; omega

end


