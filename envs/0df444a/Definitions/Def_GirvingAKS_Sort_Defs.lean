-- Prove2me | Definitions.Def_GirvingAKS_Sort_Defs
-- name    : GirvingAKS_Sort_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:29:57.965394+00:00
-- url     : https://prove2.me/theorems/aebf0b47-2750-4997-8e4f-59d922e363bf
-- title:
--   AKS sorting networks (Seiferas port) — Comparator Network Definitions
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Core definitions for comparator networks: comparators, networks, execution, embedding, injectivity preservation, and asymptotic notation.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Misc_Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Comparator Network Definitions

  Core definitions for comparator networks: comparators, networks, execution,
  embedding, injectivity preservation, and asymptotic notation.
-/



section


open Finset BigOperators


/-! **Comparator Networks** -/

/-- A comparator on `n` wires swaps positions `i` and `j` if out of order. -/
structure Comparator (n : ℕ) where
  i : Fin n
  j : Fin n
  h : i < j

/-- Apply a single comparator to a vector. -/
def Comparator.apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : Fin n → α :=
  fun k ↦
    if k = c.i then min (v c.i) (v c.j)
    else if k = c.j then max (v c.i) (v c.j)
    else v k

/-- A comparator network is a sequence of comparators applied in order. -/
@[ext] structure ComparatorNetwork (n : ℕ) where
  comparators : List (Comparator n)

/-- The size of a network is the total number of comparators. -/
def ComparatorNetwork.size {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  net.comparators.length

/-- Execute an entire comparator network on an input vector. -/
def ComparatorNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v


/-! **Comparator Network Embedding** -/

/-- Shift all comparator indices by `offset` and embed into a larger network.
    Maps each comparator `(i, j)` to `(offset + i, offset + j)`. -/
def ComparatorNetwork.shiftEmbed {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) : ComparatorNetwork n :=
  { comparators := net.comparators.map fun c ↦
      { i := ⟨offset + c.i.val, by omega⟩
        j := ⟨offset + c.j.val, by omega⟩
        h := by show offset + c.i.val < offset + c.j.val
                have := c.h; simp only [Fin.lt_def] at this; omega } }

theorem ComparatorNetwork.shiftEmbed_size {m : ℕ} (net : ComparatorNetwork m)
    (n offset : ℕ) (h : offset + m ≤ n) :
    (net.shiftEmbed n offset h).size = net.size := by
  simp [shiftEmbed, size, List.length_map]


/-! **Injectivity Preservation** -/

/-- A single comparator preserves injectivity: either no swap (identity)
    or a transposition, both of which compose injectively. -/
theorem Comparator.apply_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (c.apply v) := by
  by_cases h : v c.i ≤ v c.j
  · -- No swap: c.apply v = v
    suffices heq : c.apply v = v by rw [heq]; exact hv
    ext k; unfold Comparator.apply
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_left h]
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_right h]
      · rw [if_neg hkj]
  · -- Swap: c.apply v = v ∘ Equiv.swap c.i c.j
    push_neg at h
    suffices heq : c.apply v = v ∘ ⇑(Equiv.swap c.i c.j) by
      rw [heq]; exact hv.comp (Equiv.injective _)
    ext k; unfold Comparator.apply; simp only [Function.comp]
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_right h.le, Equiv.swap_apply_left]
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_left h.le, Equiv.swap_apply_right]
      · rw [if_neg hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Executing a comparator network preserves injectivity. -/
theorem ComparatorNetwork.exec_injective {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) {v : Fin n → α} (hv : Function.Injective v) :
    Function.Injective (net.exec v) := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact hv
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (c.apply_injective hv)

/-! **Monotone composition** -/

/-- A single comparator commutes with monotone functions: applying a comparator
    to `g ∘ v` gives `g ∘ (comparator applied to v)` when `g` is monotone.
    This is because `min(g a, g b) = g(min(a,b))` and `max(g a, g b) = g(max(a,b))`
    for monotone `g`. -/
private theorem Comparator.apply_comp_mono {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]
    (c : Comparator n) {g : α → β} (hg : Monotone g) (v : Fin n → α) :
    c.apply (g ∘ v) = g ∘ (c.apply v) := by
  ext k
  simp only [Comparator.apply, Function.comp]
  by_cases hki : k = c.i
  · subst hki; rw [if_pos rfl, if_pos rfl, hg.map_min]
  · rw [if_neg hki, if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj; rw [if_pos rfl, if_pos rfl, hg.map_max]
    · rw [if_neg hkj, if_neg hkj]

/-- Monotone functions commute with comparator network execution:
    `net.exec (g ∘ v) = g ∘ (net.exec v)` when `g` is monotone.

    This generalizes the 0-1 principle: a comparator network operates
    identically (up to order-preserving relabeling) regardless of the
    actual values; only the relative order matters. -/
theorem ComparatorNetwork.exec_comp_mono {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]
    (net : ComparatorNetwork n) {g : α → β} (hg : Monotone g) (v : Fin n → α) :
    net.exec (g ∘ v) = g ∘ (net.exec v) := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [c.apply_comp_mono hg v, ih (c.apply v)]


/-- Executing a concatenated comparator list equals sequential execution. -/
theorem ComparatorNetwork.exec_append {n : ℕ} {α : Type*} [LinearOrder α]
    (net₁ net₂ : ComparatorNetwork n) (v : Fin n → α) :
    (⟨net₁.comparators ++ net₂.comparators⟩ : ComparatorNetwork n).exec v =
    net₂.exec (net₁.exec v) := by
  simp [ComparatorNetwork.exec, List.foldl_append]

/-- Folding comparators that don't touch position `j` leaves `v j` unchanged. -/
theorem foldl_comparators_outside {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) (j : Fin n)
    (hj : ∀ c ∈ cs, j ≠ c.i ∧ j ≠ c.j) :
    cs.foldl (fun acc c ↦ c.apply acc) v j = v j := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have ⟨hji, hjj⟩ := hj c (.head cs)
    have hstep : c.apply v j = v j := by
      unfold Comparator.apply; rw [if_neg hji, if_neg hjj]
    rw [ih (c.apply v) (fun c' hc' => hj c' (.tail c hc')), hstep]

/-- A shifted+embedded network does not modify positions outside its range. -/
theorem ComparatorNetwork.shiftEmbed_exec_outside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : ℕ) (h : offset + m ≤ n)
    (v : Fin n → α) (j : Fin n) (hj : j.val < offset ∨ offset + m ≤ j.val) :
    (net.shiftEmbed n offset h).exec v j = v j := by
  unfold shiftEmbed exec
  apply foldl_comparators_outside
  intro c' hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, _, rfl⟩ := hc'
  exact ⟨by intro heq; have := congr_arg Fin.val heq; dsimp at this; omega,
         by intro heq; have := congr_arg Fin.val heq; dsimp at this; omega⟩


/-- A shifted comparator acts on positions within the range exactly as the original
    comparator on the local view `fun j ↦ v ⟨offset + j, _⟩`. -/
private theorem shifted_comparator_localView {m n : ℕ} {α : Type*} [LinearOrder α]
    {offset : ℕ} (h : offset + m ≤ n) (c : Comparator m) (v : Fin n → α) :
    let c' : Comparator n :=
      ⟨⟨offset + c.i.val, by have := c.i.isLt; omega⟩,
       ⟨offset + c.j.val, by have := c.j.isLt; omega⟩,
       by show offset + c.i.val < offset + c.j.val
          have := c.h; simp only [Fin.lt_def] at this; omega⟩
    (fun (j : Fin m) ↦ c'.apply v ⟨offset + j.val, by have := j.isLt; omega⟩) =
    c.apply (fun j ↦ v ⟨offset + j.val, by have := j.isLt; omega⟩) := by
  intro c'
  funext j
  simp only [Comparator.apply]
  by_cases hji : j = c.i
  · -- j = c.i: both sides give min
    have h_eq_i : (⟨offset + j.val, by have := j.isLt; omega⟩ : Fin n) = c'.i := by
      ext; dsimp [c']; rw [hji]
    rw [if_pos h_eq_i, if_pos hji]
  · have hne_i : (⟨offset + j.val, by have := j.isLt; omega⟩ : Fin n) ≠ c'.i := by
      intro heq; apply hji; ext
      have := congr_arg Fin.val heq; dsimp [c'] at this; omega
    rw [if_neg hne_i, if_neg hji]
    by_cases hjj : j = c.j
    · -- j = c.j: both sides give max
      have h_eq_j : (⟨offset + j.val, by have := j.isLt; omega⟩ : Fin n) = c'.j := by
        ext; dsimp [c']; rw [hjj]
      rw [if_pos h_eq_j, if_pos hjj]
    · have hne_j : (⟨offset + j.val, by have := j.isLt; omega⟩ : Fin n) ≠ c'.j := by
        intro heq; apply hjj; ext
        have := congr_arg Fin.val heq; dsimp [c'] at this; omega
      rw [if_neg hne_j, if_neg hjj]

/-- A shifted+embedded network acts on positions within its range `[offset, offset+m)`
    exactly as the original network on the local view. -/
theorem ComparatorNetwork.shiftEmbed_exec_inside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : ℕ) (h : offset + m ≤ n)
    (v : Fin n → α) (i : Fin m) :
    (net.shiftEmbed n offset h).exec v ⟨offset + i.val, by have := i.isLt; omega⟩ =
    net.exec (fun (j : Fin m) ↦ v ⟨offset + j.val, by have := j.isLt; omega⟩) i := by
  -- Prove the stronger function-level statement by induction
  suffices hfun : ∀ (cs : List (Comparator m)) (v : Fin n → α),
      (fun (j : Fin m) ↦
        (cs.map fun c ↦ (⟨⟨offset + c.i.val, by have := c.i.isLt; omega⟩,
          ⟨offset + c.j.val, by have := c.j.isLt; omega⟩,
          by show offset + c.i.val < offset + c.j.val
             have := c.h; simp only [Fin.lt_def] at this; omega⟩ : Comparator n)).foldl
        (fun acc c ↦ c.apply acc) v ⟨offset + j.val, by have := j.isLt; omega⟩) =
      cs.foldl (fun acc c ↦ c.apply acc)
        (fun j ↦ v ⟨offset + j.val, by have := j.isLt; omega⟩) from
    show _ = _ from congr_fun (hfun net.comparators v) i
  intro cs
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    exact shifted_comparator_localView h c v


/-! **Scatter Embedding** -/

/-- Embed a network on `m` wires into `n` wires via an order embedding.
    Maps comparator `(i, j)` to `(f(i), f(j))`. Generalizes `shiftEmbed`
    to non-contiguous wire positions. -/
def ComparatorNetwork.scatterEmbed {m : ℕ} (net : ComparatorNetwork m)
    (n : ℕ) (f : Fin m ↪o Fin n) : ComparatorNetwork n where
  comparators := net.comparators.map fun c ↦
    { i := f c.i, j := f c.j, h := f.lt_iff_lt.mpr c.h }

theorem ComparatorNetwork.scatterEmbed_size {m : ℕ} (net : ComparatorNetwork m)
    (n : ℕ) (f : Fin m ↪o Fin n) :
    (net.scatterEmbed n f).size = net.size := by
  simp [scatterEmbed, size, List.length_map]

/-- A scatter-embedded network does not modify positions outside the embedding's range. -/
theorem ComparatorNetwork.scatterEmbed_exec_outside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (v : Fin n → α) (j : Fin n) (hj : j ∉ Set.range f) :
    (net.scatterEmbed n f).exec v j = v j := by
  unfold scatterEmbed exec
  apply foldl_comparators_outside
  intro c' hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, _, rfl⟩ := hc'
  exact ⟨fun heq ↦ hj ⟨c.i, heq.symm⟩, fun heq ↦ hj ⟨c.j, heq.symm⟩⟩

/-- A scatter-embedded comparator acts on positions within the embedding's range exactly
    as the original comparator on the local view `v ∘ f`. -/
private theorem scattered_comparator_localView {m n : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin m ↪o Fin n) (c : Comparator m) (v : Fin n → α) :
    let c' : Comparator n := ⟨f c.i, f c.j, f.lt_iff_lt.mpr c.h⟩
    (fun (j : Fin m) ↦ c'.apply v (f j)) = c.apply (v ∘ f) := by
  intro c'
  funext j
  simp only [Comparator.apply, Function.comp]
  by_cases hji : j = c.i
  · subst hji; rw [if_pos rfl, if_pos rfl]
  · have hne_i : f j ≠ f c.i := fun h ↦ hji (f.injective h)
    rw [if_neg hne_i, if_neg hji]
    by_cases hjj : j = c.j
    · subst hjj; rw [if_pos rfl, if_pos rfl]
    · have hne_j : f j ≠ f c.j := fun h ↦ hjj (f.injective h)
      rw [if_neg hne_j, if_neg hjj]

/-- A scatter-embedded network acts on positions within its range `f(i)`
    exactly as the original network on the local view `v ∘ f`. -/
theorem ComparatorNetwork.scatterEmbed_exec_inside {m : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (v : Fin n → α) (i : Fin m) :
    (net.scatterEmbed n f).exec v (f i) = net.exec (v ∘ f) i := by
  suffices hfun : ∀ (cs : List (Comparator m)) (v : Fin n → α),
      (fun (j : Fin m) ↦
        (cs.map fun c ↦ (⟨f c.i, f c.j, f.lt_iff_lt.mpr c.h⟩ : Comparator n)).foldl
        (fun acc c ↦ c.apply acc) v (f j)) =
      cs.foldl (fun acc c ↦ c.apply acc) (v ∘ f) from
    show _ = _ from congr_fun (hfun net.comparators v) i
  intro cs
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    exact scattered_comparator_localView f c v


/-- Appending a network that doesn't touch position j (second position). -/
theorem ComparatorNetwork.exec_append_outside' {n : ℕ} {α : Type*} [LinearOrder α]
    (net₁ net₂ : ComparatorNetwork n) (v : Fin n → α) (j : Fin n)
    (hj : ∀ c ∈ net₂.comparators, j ≠ c.i ∧ j ≠ c.j) :
    (⟨net₁.comparators ++ net₂.comparators⟩ : ComparatorNetwork n).exec v j =
    net₁.exec v j := by
  rw [exec_append]
  unfold exec
  exact foldl_comparators_outside net₂.comparators (net₁.exec v) j hj

/-- Executing a flatMap of comparators from scatter-embedded networks equals
    sequential execution of those networks. -/
theorem ComparatorNetwork.exec_flatMap {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α) :
    (⟨xs.flatMap fun i ↦ (f i).comparators⟩ : ComparatorNetwork n).exec v =
    xs.foldl (fun v' i ↦ (f i).exec v') v := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_cons]
    rw [← ih]
    exact exec_append (f x) ⟨xs.flatMap fun i ↦ (f i).comparators⟩ v

/-- Folding execution of networks that don't touch j leaves j unchanged. -/
theorem ComparatorNetwork.foldl_exec_outside {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α)
    (j : Fin n) (hj : ∀ a ∈ xs, ∀ c ∈ (f a).comparators, j ≠ c.i ∧ j ≠ c.j) :
    xs.foldl (fun v' a ↦ (f a).exec v') v j = v j := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hxs : ∀ a ∈ xs, ∀ c ∈ (f a).comparators, j ≠ c.i ∧ j ≠ c.j :=
      fun a ha ↦ hj a (List.mem_cons_of_mem x ha)
    rw [ih _ hxs]
    unfold exec
    exact foldl_comparators_outside (f x).comparators v j (hj x List.mem_cons_self)

/-- Folding execution of networks that don't touch any position in S preserves all values in S. -/
theorem ComparatorNetwork.foldl_exec_outside_set {n : ℕ} {α : Type*} [LinearOrder α]
    {ι : Type*} (xs : List ι) (f : ι → ComparatorNetwork n) (v : Fin n → α)
    (S : Finset (Fin n)) (hS : ∀ a ∈ xs, ∀ s ∈ S, ∀ c ∈ (f a).comparators, s ≠ c.i ∧ s ≠ c.j) :
    ∀ s ∈ S, xs.foldl (fun v' a ↦ (f a).exec v') v s = v s := by
  intro s hs
  exact foldl_exec_outside xs f v s (fun a ha c hc ↦ hS a ha s hs c hc)

/-- A scatter-embedded network's comparators don't touch positions outside the range. -/
theorem ComparatorNetwork.scatterEmbed_comparators_outside {m : ℕ}
    (net : ComparatorNetwork m) (n : ℕ) (f : Fin m ↪o Fin n)
    (j : Fin n) (hj : j ∉ Set.range f) (c : Comparator n)
    (hc : c ∈ (net.scatterEmbed n f).comparators) :
    j ≠ c.i ∧ j ≠ c.j := by
  simp only [scatterEmbed, List.mem_map] at hc
  obtain ⟨c', _, rfl⟩ := hc
  exact ⟨fun heq ↦ hj ⟨c'.i, heq.symm⟩, fun heq ↦ hj ⟨c'.j, heq.symm⟩⟩

/-! **Complexity Notation** -/

/-- Asymptotic notation for stating complexity bounds. -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (n₀ : ℕ), C > 0 ∧ ∀ n, n ≥ n₀ → |f n| ≤ C * |g n|

notation f " =O(" g ")" => IsBigO f g

end


