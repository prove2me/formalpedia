-- Prove2me | Definitions.Def_GirvingAKS_Sort_Depth
-- name    : GirvingAKS_Sort_Depth
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:24.132909+00:00
-- url     : https://prove2.me/theorems/86110728-d941-42ee-8885-e1b6c217add3
-- title:
--   AKS sorting networks (Seiferas port) — Comparator Network Depth
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Depth.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Depth (minimum parallel rounds) of a comparator network. The AKS (1983) network achieves O(log n) depth in addition to O(n log n) size.
--
--   Main results:
--
--   - `ComparatorNetwork.depth` : Critical-path depth via greedy scheduling.
--   - `depth_nil`               : Empty network has depth 0.
--   - `depth_le_size`           : Depth is at most the number of comparators.
--   - `depth_le_of_decomposition` : Any parallel decomposition upper-bounds depth.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Depth.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Depth.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Comparator Network Depth

  Depth (minimum parallel rounds) of a comparator network.
  The AKS (1983) network achieves O(log n) depth in addition to O(n log n) size.

  Main results:
  • `ComparatorNetwork.depth` : Critical-path depth via greedy scheduling.
  • `depth_nil`               : Empty network has depth 0.
  • `depth_le_size`           : Depth is at most the number of comparators.
  • `depth_le_of_decomposition` : Any parallel decomposition upper-bounds depth.
-/


section


open Finset BigOperators


/-! **Comparator Overlap** -/

/-- Two comparators overlap if they share a wire. -/
def Comparator.overlaps {n : ℕ} (c₁ c₂ : Comparator n) : Prop :=
  c₁.i = c₂.i ∨ c₁.i = c₂.j ∨ c₁.j = c₂.i ∨ c₁.j = c₂.j

instance {n : ℕ} (c₁ c₂ : Comparator n) : Decidable (c₁.overlaps c₂) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))


/-! **Network Depth** -/

def depthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.i) (wt c.j) + 1
  (Function.update (Function.update wt c.i t) c.j t, max state.2 t)

/-- The depth of a comparator network, computed via greedy critical-path scheduling.

    Each comparator is assigned time step `max(wireTime c.i, wireTime c.j) + 1`,
    then both wires are updated to that time. The network depth is the maximum
    assigned time step.

    This is an upper bound on the minimum number of parallel rounds needed to
    execute the network (see `depth_le_of_decomposition`). -/
def ComparatorNetwork.depth {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2


/-! **Basic Properties** -/

/-- The empty network has depth 0. -/
theorem depth_nil {n : ℕ} : (⟨[]⟩ : ComparatorNetwork n).depth = 0 := by
  simp [ComparatorNetwork.depth]

/-- After processing `cs` starting from `(wt, d)` with `∀ k, wt k ≤ d`,
    the running max is at most `d + cs.length`. -/
lemma depth_foldl_le_length {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (d : ℕ) (hwt : ∀ k, wt k ≤ d) :
    (cs.foldl depthStep (wt, d)).2 ≤ d + cs.length := by
  induction cs generalizing wt d with
  | nil => simp [List.foldl]
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hi := hwt c.i
    have hj := hwt c.j
    have hwt' : ∀ k, (depthStep (wt, d) c).1 k ≤ (depthStep (wt, d) c).2 := by
      intro k; have hk := hwt k
      simp only [depthStep, Function.update_apply]
      split_ifs <;> omega
    have hd' : (depthStep (wt, d) c).2 ≤ d + 1 := by
      simp only [depthStep]; omega
    have step := ih ((depthStep (wt, d) c).1) ((depthStep (wt, d) c).2) hwt'
    rw [Prod.mk.eta] at step
    omega

/-- Network depth is at most the number of comparators. -/
theorem depth_le_size {n : ℕ} (net : ComparatorNetwork n) :
    net.depth ≤ net.size := by
  unfold ComparatorNetwork.depth ComparatorNetwork.size
  have h := depth_foldl_le_length net.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_refl 0)
  simp at h
  exact h


/-! **Parallel Decomposition** -/

/-- A layer is a list of pairwise non-overlapping comparators. -/
def IsParallelLayer {n : ℕ} (layer : List (Comparator n)) : Prop :=
  layer.Pairwise (fun c₁ c₂ ↦ ¬c₁.overlaps c₂)

/-- A parallel decomposition of a network is a list of layers whose
    concatenation (in order) equals the network's comparator list. -/
def IsParallelDecomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n))) : Prop :=
  (∀ layer ∈ layers, IsParallelLayer layer) ∧
    layers.flatten = net.comparators


/-! **Depth Upper Bound from Parallel Decomposition** -/

/-- `depthStep` for a non-overlapping comparator preserves the other's wire times. -/
lemma depthStep_preserves_nonoverlap {n : ℕ}
    {c₁ c₂ : Comparator n} (hno : ¬c₁.overlaps c₂)
    (wt : Fin n → ℕ) (d : ℕ) :
    (depthStep (wt, d) c₁).1 c₂.i = wt c₂.i ∧
    (depthStep (wt, d) c₁).1 c₂.j = wt c₂.j := by
  unfold Comparator.overlaps at hno; push_neg at hno
  obtain ⟨h1, h2, h3, h4⟩ := hno
  simp only [depthStep, Function.update_apply]
  refine ⟨?_, ?_⟩
  · rw [if_neg (Ne.symm h3), if_neg (Ne.symm h1)]
  · rw [if_neg (Ne.symm h4), if_neg (Ne.symm h2)]

/-- Processing one non-overlapping layer: if all wire times relevant to the
    layer's comparators are ≤ `d`, then afterward all wire times are ≤ `d + 1`
    and the running max is ≤ `d + 1`.

    Key invariant: within a non-overlapping layer, each comparator's wires
    haven't been touched by earlier comparators in the same layer (since they
    don't share any wires), so they still see the pre-layer bound `d`. -/
lemma layer_foldl_bound {n : ℕ} (cs : List (Comparator n))
    (hcs : IsParallelLayer cs)
    (wt : Fin n → ℕ) (d dm : ℕ)
    (hwt_layer : ∀ c ∈ cs, wt c.i ≤ d ∧ wt c.j ≤ d)
    (hwt_all : ∀ k, wt k ≤ d + 1)
    (hdm : dm ≤ d + 1) :
    (∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ d + 1) ∧
    (cs.foldl depthStep (wt, dm)).2 ≤ d + 1 := by
  induction cs generalizing wt dm with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨hwt_all, hdm⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hci, hcj⟩ := hwt_layer c (List.mem_cons.mpr (.inl rfl))
    have hcs_tail := (List.pairwise_cons.mp hcs).2
    have hc_nonoverlap := (List.pairwise_cons.mp hcs).1
    -- After processing c: all wire times ≤ d + 1
    have hwt_all' : ∀ k, (depthStep (wt, dm) c).1 k ≤ d + 1 := by
      intro k; have hk := hwt_all k
      simp only [depthStep, Function.update_apply]
      split_ifs <;> omega
    have hdm' : (depthStep (wt, dm) c).2 ≤ d + 1 := by
      simp only [depthStep]; omega
    -- For remaining comparators, their wires are unchanged (non-overlapping with c)
    have hwt_layer' : ∀ c' ∈ cs, (depthStep (wt, dm) c).1 c'.i ≤ d ∧
        (depthStep (wt, dm) c).1 c'.j ≤ d := by
      intro c' hc'
      have ⟨hpi, hpj⟩ := depthStep_preserves_nonoverlap (hc_nonoverlap c' hc') wt dm
      have ⟨hi', hj'⟩ := hwt_layer c' (List.mem_cons_of_mem c hc')
      exact ⟨hpi ▸ hi', hpj ▸ hj'⟩
    exact ih hcs_tail _ _ hwt_layer' hwt_all' hdm'

/-- Processing multiple layers starting from wire times ≤ d gives depth ≤ d + layers.length. -/
lemma layers_foldl_bound {n : ℕ} (layers : List (List (Comparator n)))
    (hlayers : ∀ layer ∈ layers, IsParallelLayer layer)
    (wt : Fin n → ℕ) (d dm : ℕ)
    (hwt : ∀ k, wt k ≤ d) (hdm : dm ≤ d) :
    (layers.flatten.foldl depthStep (wt, dm)).2 ≤ d + layers.length := by
  induction layers generalizing wt d dm with
  | nil =>
    simp only [List.flatten_nil, List.foldl_nil, List.length_nil, Nat.add_zero]
    exact hdm
  | cons layer layers ih =>
    have hpar := hlayers layer (List.mem_cons.mpr (.inl rfl))
    have hlayers' : ∀ l ∈ layers, IsParallelLayer l :=
      fun l hl ↦ hlayers l (List.mem_cons_of_mem layer hl)
    -- Unfold flatten and use foldl_append to split into layer ++ rest
    simp only [List.flatten_cons, List.foldl_append, List.length_cons]
    -- After processing one layer: wire times ≤ d + 1
    have hwt_layer : ∀ c ∈ layer, wt c.i ≤ d ∧ wt c.j ≤ d :=
      fun c _ ↦ ⟨hwt c.i, hwt c.j⟩
    have hwt_d1 : ∀ k, wt k ≤ d + 1 := fun k ↦ Nat.le_succ_of_le (hwt k)
    have hdm1 : dm ≤ d + 1 := Nat.le_succ_of_le hdm
    have bound := layer_foldl_bound layer hpar wt d dm hwt_layer hwt_d1 hdm1
    -- Apply IH with d' = d + 1
    have step := ih hlayers' _ (d + 1) _ bound.1 bound.2
    rw [Prod.mk.eta] at step
    omega

/-- **Any parallel decomposition upper-bounds depth.** If a network can be
    decomposed into `k` layers of pairwise non-overlapping comparators, then
    its greedy depth is at most `k`. -/
theorem depth_le_of_decomposition {n : ℕ} (net : ComparatorNetwork n)
    (layers : List (List (Comparator n)))
    (hd : IsParallelDecomposition net layers) :
    net.depth ≤ layers.length := by
  unfold ComparatorNetwork.depth
  rw [← hd.2]
  have h := layers_foldl_bound layers hd.1 (fun _ ↦ 0) 0 0
    (fun _ ↦ le_refl 0) (le_refl 0)
  omega


/-! **Size–Depth Bound** -/

/-- Updating at index `i` and summing: the new sum plus the old value at `i`
    equals the old sum plus the new value. -/
lemma sum_update_add {n : ℕ} (f : Fin n → ℕ) (i : Fin n) (v : ℕ) :
    ∑ k : Fin n, Function.update f i v k + f i = ∑ k : Fin n, f k + v := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update f i v) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  rw [Function.update_self] at h1
  have h3 : ∑ x ∈ Finset.univ.erase i, Function.update f i v x =
      ∑ x ∈ Finset.univ.erase i, f x :=
    Finset.sum_congr rfl fun k hk ↦
      Function.update_of_ne (Finset.ne_of_mem_erase hk) v f
  omega

/-- A single `depthStep` increases `∑ wt` by at least 2. -/
lemma depthStep_sum_ge {n : ℕ} (wt : Fin n → ℕ) (dm : ℕ) (c : Comparator n) :
    ∑ k : Fin n, wt k + 2 ≤ ∑ k : Fin n, (depthStep (wt, dm) c).1 k := by
  simp only [depthStep]
  set t := max (wt c.i) (wt c.j) + 1
  have hne : c.i ≠ c.j := Fin.ne_of_lt c.h
  have h1 := sum_update_add wt c.i t
  have h2 := sum_update_add (Function.update wt c.i t) c.j t
  rw [Function.update_of_ne hne.symm t wt] at h2
  -- h1: ∑ (update wt i t) + wt i = ∑ wt + t
  -- h2: ∑ (double update) + wt j = ∑ (update wt i t) + t
  -- ht: wt i + wt j + 2 ≤ 2 * t
  have ht : wt c.i + wt c.j + 2 ≤ 2 * t := by simp only [t]; omega
  omega

/-- Through a full foldl, `∑ wt` increases by at least `2 * cs.length`. -/
lemma foldl_sum_increase {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) :
    ∑ k : Fin n, wt k + 2 * cs.length ≤
    ∑ k : Fin n, (cs.foldl depthStep (wt, dm)).1 k := by
  induction cs generalizing wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h_step := depthStep_sum_ge wt dm c
    have h_rest := ih (depthStep (wt, dm) c).1 (depthStep (wt, dm) c).2
    rw [Prod.mk.eta] at h_rest
    omega

/-- Wire times are bounded by the running max throughout the fold. -/
lemma wt_le_running_max {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) (hwt : ∀ k, wt k ≤ dm) :
    ∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤ (cs.foldl depthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact hwt
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro k
    have hk := hwt k
    set t := max (wt c.i) (wt c.j) + 1
    by_cases hkj : k = c.j
    · subst hkj; rw [Function.update_self]; exact le_max_right dm t
    · rw [Function.update_of_ne hkj t (Function.update wt c.i t)]
      by_cases hki : k = c.i
      · subst hki; rw [Function.update_self]; exact le_max_right dm t
      · rw [Function.update_of_ne hki t wt]
        exact le_trans hk (le_max_left dm t)

/-- **Size–depth bound**: `2 * size ≤ n * depth` for any comparator network.
    Each comparator uses 2 of the `n` wires, contributing ≥ 2 to the total
    wire-time sum. The sum is bounded by `n * depth` since each wire ends
    at time ≤ depth. -/
theorem size_le_half_n_mul_depth {n : ℕ} (net : ComparatorNetwork n) :
    2 * net.size ≤ n * net.depth := by
  unfold ComparatorNetwork.depth ComparatorNetwork.size
  have h_sum := foldl_sum_increase net.comparators (fun _ ↦ 0) 0
  simp only [Finset.sum_const_zero, zero_add] at h_sum
  have h_wt := wt_le_running_max net.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_refl 0)
  have h_bound : ∑ k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).1 k ≤
      n * (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 := by
    calc ∑ k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).1 k
        ≤ ∑ _k : Fin n, (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 :=
          Finset.sum_le_sum fun k _ ↦ h_wt k
      _ = n * (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2 := by
          simp [Finset.sum_const, Finset.card_univ]
  omega


/-! **Depth of Concatenated Networks** -/

/-- Pointwise shift bound: if initial wire times and running max are offset by `d`
    from a reference state, then after processing `cs`, the outputs are still offset
    by at most `d`. This is the key invariant for `depth_append`. -/
lemma foldl_depth_pointwise_shift {n : ℕ} (cs : List (Comparator n))
    (wt wt₀ : Fin n → ℕ) (dm dm₀ d : ℕ)
    (hwt : ∀ k, wt k ≤ d + wt₀ k) (hdm : dm ≤ d + dm₀) :
    (∀ k, (cs.foldl depthStep (wt, dm)).1 k ≤
      d + (cs.foldl depthStep (wt₀, dm₀)).1 k) ∧
    (cs.foldl depthStep (wt, dm)).2 ≤
      d + (cs.foldl depthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact ⟨hwt, hdm⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    · -- Wire times after one step: pointwise shift preserved
      intro k
      simp only [Function.update_apply]
      have hk := hwt k; have hi := hwt c.i; have hj := hwt c.j
      split_ifs <;> omega
    · -- Running max after one step: shift preserved
      dsimp only []
      have hi := hwt c.i; have hj := hwt c.j
      omega

/-- **Depth of concatenated networks.** The depth of `net₁ ++ net₂` is at most
    `net₁.depth + net₂.depth`: the second network starts where the first left off. -/
theorem depth_append {n : ℕ} (net₁ net₂ : ComparatorNetwork n) :
    (⟨net₁.comparators ++ net₂.comparators⟩ : ComparatorNetwork n).depth ≤
    net₁.depth + net₂.depth := by
  simp only [ComparatorNetwork.depth]
  rw [List.foldl_append]
  -- After net₁: wire times ≤ net₁.depth (the running max)
  set d₁ := (net₁.comparators.foldl depthStep (fun _ ↦ 0, 0)).2
  have hwt := wt_le_running_max net₁.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_refl 0)
  -- Apply pointwise shift with reference state (0, 0) and offset d₁
  have h := (foldl_depth_pointwise_shift net₂.comparators
    (net₁.comparators.foldl depthStep (fun _ ↦ 0, 0)).1
    (fun _ ↦ 0) d₁ 0 d₁
    (fun k ↦ by simp [d₁]; exact hwt k)
    (le_refl _)).2
  rw [Prod.mk.eta] at h
  exact h


/-! **Depth of Shifted/Embedded Networks** -/

/-- Processing shifted comparators maintains the running max: the depth of
    shifted comparators equals the depth of original comparators, because
    `depthStep` only cares about which wires overlap, not their absolute indices.

    Invariant: `wt` on `Fin n` corresponds to `wt₀` on `Fin m` at positions
    `[offset, offset+m)`, and is 0 elsewhere. -/
lemma foldl_shiftEmbed_eq {m n : ℕ} (cs : List (Comparator m))
    (offset : ℕ) (h : offset + m ≤ n) (wt₀ : Fin m → ℕ) (wt : Fin n → ℕ) (dm : ℕ)
    (hwt : ∀ j : Fin m, wt ⟨offset + j.val, by omega⟩ = wt₀ j) :
    let shifted := cs.map fun c ↦
      (⟨⟨offset + c.i.val, by omega⟩,
        ⟨offset + c.j.val, by omega⟩,
        by show offset + c.i.val < offset + c.j.val
           have := c.h; simp only [Fin.lt_def] at this; omega⟩ : Comparator n)
    (shifted.foldl depthStep (wt, dm)).2 = (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    -- Abbreviate the shifted comparator
    set c' : Comparator n :=
      ⟨⟨offset + c.i.val, by omega⟩, ⟨offset + c.j.val, by omega⟩, by
        show offset + c.i.val < offset + c.j.val
        have := c.h; simp only [Fin.lt_def] at this; omega⟩
    -- Wire times at shifted positions equal original wire times (by proof irrelevance)
    have h_ci : wt c'.i = wt₀ c.i := hwt c.i
    have h_cj : wt c'.j = wt₀ c.j := hwt c.j
    -- Running max after one step is equal
    have hdm_eq : (depthStep (wt, dm) c').2 = (depthStep (wt₀, dm) c).2 := by
      simp only [depthStep, h_ci, h_cj]
    -- Wire times after one step correspond at shifted positions
    have hwt_step : ∀ j : Fin m,
        (depthStep (wt, dm) c').1 ⟨offset + j.val, by omega⟩ =
        (depthStep (wt₀, dm) c).1 j := by
      intro j
      simp only [depthStep, Function.update_apply, h_ci, h_cj]
      by_cases hjj : j = c.j
      · have : (⟨offset + j.val, by omega⟩ : Fin n) = c'.j := by subst hjj; rfl
        rw [if_pos this, if_pos hjj]
      · have : (⟨offset + j.val, by omega⟩ : Fin n) ≠ c'.j := by
          intro heq; apply hjj; ext
          have := congr_arg Fin.val heq; simp [c'] at this; omega
        rw [if_neg this, if_neg hjj]
        by_cases hji : j = c.i
        · have : (⟨offset + j.val, by omega⟩ : Fin n) = c'.i := by subst hji; rfl
          rw [if_pos this, if_pos hji]
        · have : (⟨offset + j.val, by omega⟩ : Fin n) ≠ c'.i := by
            intro heq; apply hji; ext
            have := congr_arg Fin.val heq; simp [c'] at this; omega
          rw [if_neg this, if_neg hji, hwt j]
    -- Apply IH: use c'.2 as the running max so Prod.mk.eta works on the LHS
    have step := ih (depthStep (wt₀, dm) c).1 (depthStep (wt, dm) c').1
      (depthStep (wt, dm) c').2 hwt_step
    simp only at step
    rw [Prod.mk.eta] at step
    rw [hdm_eq, Prod.mk.eta] at step
    exact step

/-- **Depth is preserved by shift embedding.** Shifting comparator indices
    by an offset doesn't change the critical-path depth, since the depth
    scheduling only depends on which wires overlap. -/
theorem depth_shiftEmbed_le {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) :
    (net.shiftEmbed n offset h).depth ≤ net.depth := by
  simp only [ComparatorNetwork.depth, ComparatorNetwork.shiftEmbed]
  have := foldl_shiftEmbed_eq net.comparators offset h (fun _ ↦ 0) (fun _ ↦ 0) 0
    (fun _ ↦ rfl)
  dsimp only at this
  rw [this]


/-! **Depth of Scatter-Embedded Networks** -/

/-- Processing scatter-embedded comparators maintains the running max:
    the depth of scatter-embedded comparators equals the depth of the original,
    because `depthStep` only cares about which wires overlap.

    Invariant: `wt` on `Fin n` corresponds to `wt₀` on `Fin m` at positions
    in the image of `f`, and the running max is shared. -/
lemma foldl_scatterEmbed_eq {m n : ℕ} (cs : List (Comparator m))
    (f : Fin m ↪o Fin n) (wt₀ : Fin m → ℕ) (wt : Fin n → ℕ) (dm : ℕ)
    (hwt : ∀ j : Fin m, wt (f j) = wt₀ j) :
    let scattered := cs.map fun c ↦
      ({ i := f c.i, j := f c.j, h := f.lt_iff_lt.mpr c.h } : Comparator n)
    (scattered.foldl depthStep (wt, dm)).2 = (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    set c' : Comparator n :=
      { i := f c.i, j := f c.j, h := f.lt_iff_lt.mpr c.h }
    -- Wire times at mapped positions equal original wire times
    have h_ci : wt c'.i = wt₀ c.i := hwt c.i
    have h_cj : wt c'.j = wt₀ c.j := hwt c.j
    -- Running max after one step is equal
    have hdm_eq : (depthStep (wt, dm) c').2 = (depthStep (wt₀, dm) c).2 := by
      simp only [depthStep, h_ci, h_cj]
    -- Wire times after one step correspond at mapped positions
    have hwt_step : ∀ j : Fin m,
        (depthStep (wt, dm) c').1 (f j) = (depthStep (wt₀, dm) c).1 j := by
      intro j
      simp only [depthStep, Function.update_apply, h_ci, h_cj]
      by_cases hjj : j = c.j
      · have : f j = c'.j := by subst hjj; rfl
        rw [if_pos this, if_pos hjj]
      · have : f j ≠ c'.j := by
          intro heq; apply hjj; exact f.injective heq
        rw [if_neg this, if_neg hjj]
        by_cases hji : j = c.i
        · have : f j = c'.i := by subst hji; rfl
          rw [if_pos this, if_pos hji]
        · have : f j ≠ c'.i := by
            intro heq; apply hji; exact f.injective heq
          rw [if_neg this, if_neg hji, hwt j]
    -- Apply IH
    have step := ih (depthStep (wt₀, dm) c).1 (depthStep (wt, dm) c').1
      (depthStep (wt, dm) c').2 hwt_step
    simp only at step
    rw [Prod.mk.eta] at step
    rw [hdm_eq, Prod.mk.eta] at step
    exact step

/-- **Depth is preserved by scatter embedding.** Mapping comparator indices
    via an order embedding doesn't change the critical-path depth, since the
    depth scheduling only depends on which wires overlap. -/
theorem depth_scatterEmbed_le {m : ℕ} (net : ComparatorNetwork m)
    (n : ℕ) (f : Fin m ↪o Fin n) :
    (net.scatterEmbed n f).depth ≤ net.depth := by
  simp only [ComparatorNetwork.depth, ComparatorNetwork.scatterEmbed]
  have := foldl_scatterEmbed_eq net.comparators f (fun _ ↦ 0) (fun _ ↦ 0) 0
    (fun _ ↦ rfl)
  dsimp only at this
  rw [this]


/-! **Depth of Wire-Disjoint Chunks** -/

/-- Running max is monotone through foldl: the initial `dm` never decreases. -/
lemma foldl_dm_le {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) :
    dm ≤ (cs.foldl depthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact le_refl dm
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have h1 : dm ≤ (depthStep (wt, dm) c).2 := by
      simp only [depthStep]; exact le_max_left dm _
    exact le_trans h1 (ih _ _)

/-- Wire times are unchanged for positions not touched by any comparator. -/
lemma foldl_untouched_wire {n : ℕ} (cs : List (Comparator n))
    (wt : Fin n → ℕ) (dm : ℕ) (k : Fin n)
    (hk : ∀ c ∈ cs, k ≠ c.i ∧ k ≠ c.j) :
    (cs.foldl depthStep (wt, dm)).1 k = wt k := by
  induction cs generalizing wt dm with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hki, hkj⟩ := hk c (List.mem_cons.mpr (.inl rfl))
    have hstep : (depthStep (wt, dm) c).1 k = wt k := by
      simp only [depthStep, Function.update_apply, if_neg hkj, if_neg hki]
    rw [ih _ _ (fun c' hc' => hk c' (List.mem_cons_of_mem c hc')), hstep]

/-- When wire times agree on all wires of `cs`, the running max is bounded by
    `max dm (standalone result)`. This captures the key insight that the `t` values
    produced by `depthStep` depend only on wire times at touched positions. -/
lemma foldl_dm_max_of_agree {n : ℕ} (cs : List (Comparator n))
    (wt wt₀ : Fin n → ℕ) (dm dm₀ : ℕ)
    (hwt : ∀ c ∈ cs, wt c.i = wt₀ c.i ∧ wt c.j = wt₀ c.j) :
    (cs.foldl depthStep (wt, dm)).2 ≤
      max dm (cs.foldl depthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact le_max_left dm dm₀
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hci, hcj⟩ := hwt c (List.mem_cons.mpr (.inl rfl))
    have ht_eq : max (wt c.i) (wt c.j) = max (wt₀ c.i) (wt₀ c.j) := by
      rw [hci, hcj]
    -- Wire agreement is preserved after one depthStep
    have hwt' : ∀ c' ∈ cs, (depthStep (wt, dm) c).1 c'.i =
        (depthStep (wt₀, dm₀) c).1 c'.i ∧
        (depthStep (wt, dm) c).1 c'.j =
        (depthStep (wt₀, dm₀) c).1 c'.j := by
      intro c' hc'
      have ⟨hci', hcj'⟩ := hwt c' (List.mem_cons_of_mem c hc')
      constructor <;> {
        simp only [depthStep, Function.update_apply, ht_eq]
        split_ifs <;> first | rfl | assumption
      }
    -- Apply IH
    have step := ih (depthStep (wt, dm) c).1 (depthStep (wt₀, dm₀) c).1
      (depthStep (wt, dm) c).2 (depthStep (wt₀, dm₀) c).2 hwt'
    rw [Prod.mk.eta, Prod.mk.eta] at step
    -- Chain: LHS ≤ max dm₁ (cs_result₀) ≤ max dm (full_result₀)
    -- t = max(wt c.i, wt c.j) + 1, dm₁ = max dm t
    -- t ≤ dm₁₀ ≤ full_result₀ (via foldl_dm_le)
    have h_t_le : max (wt c.i) (wt c.j) + 1 ≤
        (cs.foldl depthStep (depthStep (wt₀, dm₀) c)).2 :=
      calc max (wt c.i) (wt c.j) + 1
          = max (wt₀ c.i) (wt₀ c.j) + 1 := by rw [hci, hcj]
        _ ≤ (depthStep (wt₀, dm₀) c).2 := by simp only [depthStep]; exact le_max_right _ _
        _ ≤ _ := foldl_dm_le cs _ _
    -- dm₁ = max dm t, so max dm₁ X ≤ max dm X when t ≤ X
    exact le_trans step (max_le
      (by simp only [depthStep]
          exact max_le (le_max_left _ _) (le_trans h_t_le (le_max_right _ _)))
      (le_max_right _ _))

/-- **Depth of wire-disjoint flatMap.** If chunks have pairwise wire-disjoint
    comparators and each chunk has depth ≤ `d`, then the concatenated network
    also has depth ≤ `d` (they execute in parallel). -/
theorem depth_flatMap_disjoint {n : ℕ} {ι : Type*}
    (chunks : List ι) (f : ι → List (Comparator n)) (d : ℕ)
    (hd : ∀ x ∈ chunks, (⟨f x⟩ : ComparatorNetwork n).depth ≤ d)
    (hdisj : chunks.Pairwise (fun a b ↦ ∀ c₁ ∈ f a, ∀ c₂ ∈ f b,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j))) :
    (⟨chunks.flatMap f⟩ : ComparatorNetwork n).depth ≤ d := by
  simp only [ComparatorNetwork.depth]
  induction chunks with
  | nil => simp [List.flatMap_nil, List.foldl_nil]
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [List.foldl_append]
    have hx_disj := (List.pairwise_cons.mp hdisj).1
    -- All wires in xs.flatMap f are untouched (still 0) after processing f(x)
    have hwt_agree : ∀ c ∈ xs.flatMap f,
        ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 c.i = (fun _ : Fin n ↦ 0) c.i ∧
        ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 c.j = (fun _ : Fin n ↦ 0) c.j := by
      intro c hc
      rw [List.mem_flatMap] at hc
      obtain ⟨y, hy, hcfy⟩ := hc
      have hxy := hx_disj y hy
      constructor
      · rw [foldl_untouched_wire]
        intro c₁ hc₁
        have := hxy c₁ hc₁ c hcfy
        exact ⟨this.1.1.symm, this.2.1.symm⟩
      · rw [foldl_untouched_wire]
        intro c₁ hc₁
        have := hxy c₁ hc₁ c hcfy
        exact ⟨this.1.2.symm, this.2.2.symm⟩
    -- Apply foldl_dm_max_of_agree: result ≤ max dm_x (standalone depth of xs.flatMap f)
    have h_bound := foldl_dm_max_of_agree (xs.flatMap f)
      ((f x).foldl depthStep (fun _ ↦ 0, 0)).1 (fun _ ↦ 0)
      ((f x).foldl depthStep (fun _ ↦ 0, 0)).2 0
      hwt_agree
    rw [Prod.mk.eta] at h_bound
    -- dm_x ≤ d (chunk x's depth) and IH: standalone ≤ d
    exact le_trans h_bound (max_le
      (hd x (List.mem_cons.mpr (.inl rfl)))
      (ih (fun y hy ↦ hd y (List.mem_cons_of_mem x hy))
          (List.pairwise_cons.mp hdisj).2))

end


