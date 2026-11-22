-- Prove2me | Definitions.Def_GirvingAKS_Halver_Mono
-- name    : GirvingAKS_Halver_Mono
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:13.414743+00:00
-- url     : https://prove2.me/theorems/45fac5ea-fcf5-4cf5-88cf-1207e1a18480
-- title:
--   AKS sorting networks (Seiferas port) — Halver Monotonicity Under Appending Comparators
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/Mono.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Appending comparators to an ε-halver preserves the halver property. Both `EpsilonInitialHalved` and `EpsilonFinalHalved` are monotone (non-increasing in error) under appending any comparator.
--
--   Key insight: a comparator `(a, b)` with `a < b` moves the min to `a` and max to `b`. For InitialHalved, the "bad" positions are `{pos : pos ≥ m}` (upward-closed in position), and `a < b` ensures that if `a` is bad then `b` is too — so swapping values between `a` and `b` can only reduce (or preserve) the count of small output values in the bad set.
--
--   Main results:
--
--   - `EpsilonInitialHalved_append` — appending preserves initial halving
--   - `EpsilonFinalHalved_append` — appending preserves final halving
--   - `EpsilonHalved_append` — appending preserves both-sided halving
--   - `IsEpsilonHalver_append` — appending to a halver network yields a halver
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/Mono.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/Mono.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Halver Monotonicity Under Appending Comparators

  Appending comparators to an ε-halver preserves the halver property.
  Both `EpsilonInitialHalved` and `EpsilonFinalHalved` are monotone
  (non-increasing in error) under appending any comparator.

  Key insight: a comparator `(a, b)` with `a < b` moves the min to `a` and
  max to `b`. For InitialHalved, the "bad" positions are `{pos : pos ≥ m}`
  (upward-closed in position), and `a < b` ensures that if `a` is bad then
  `b` is too — so swapping values between `a` and `b` can only reduce (or
  preserve) the count of small output values in the bad set.

  Main results:
  • `EpsilonInitialHalved_append` — appending preserves initial halving
  • `EpsilonFinalHalved_append` — appending preserves final halving
  • `EpsilonHalved_append` — appending preserves both-sided halving
  • `IsEpsilonHalver_append` — appending to a halver network yields a halver
-/


section

open Finset

/-! **Helper lemmas for decomposing filter counts on pairs** -/

/-- Card of a filter on a two-element set decomposes into indicators. -/
lemma card_filter_pair {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (P : α → Prop) [DecidablePred P] :
    (({a, b} : Finset α).filter P).card =
    (if P a then 1 else 0) + (if P b then 1 else 0) := by
  simp only [filter_insert, filter_singleton]
  split_ifs with ha hb <;> simp [card_pair hab]

/-- Decompose a filter on `univ` into a pair part and its complement. -/
lemma filter_decomp {n : ℕ} (c : Comparator n) (P : Fin n → Prop) [DecidablePred P] :
    (univ.filter P : Finset (Fin n)).card =
    (({c.i, c.j} : Finset (Fin n)).filter P).card +
    ((univ \ {c.i, c.j}).filter P).card := by
  conv_lhs =>
    rw [show (univ : Finset (Fin n)) = {c.i, c.j} ∪ (univ \ {c.i, c.j}) from
      (union_sdiff_of_subset (subset_univ _)).symm, filter_union]
  exact card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff)

lemma not_mem_pair_iff {α : Type*} [DecidableEq α] {a b x : α} :
    x ∉ ({a, b} : Finset α) ↔ x ≠ a ∧ x ≠ b := by
  simp [Finset.mem_insert, Finset.mem_singleton]

/-! **Core comparator monotonicity** -/

/-- Applying a single comparator can only decrease the count of positions in
    `{pos : m ≤ pos.val}` whose output value is below threshold `k`.

    The proof decomposes `univ` into `{c.i, c.j}` (where values change) and
    its complement (where values are unchanged). On the pair:
    - If `w c.i ≤ w c.j`: no swap, counts identical.
    - If `w c.i > w c.j`: values swap, but since `c.i < c.j`, the upward-closed
      set either contains both (net zero change) or only `c.j` (which receives
      the larger value, so count can only decrease). -/
theorem comparator_initialHalved_count_le {n : ℕ} (c : Comparator n)
    (w : Fin n → Fin n) (m k : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (c.apply w pos).val < k)).card ≤
    (univ.filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (w pos).val < k)).card := by
  have hij : c.i ≠ c.j := Fin.ne_of_lt c.h
  have hcompl : ∀ pos : Fin n, pos ≠ c.i → pos ≠ c.j → c.apply w pos = w pos := by
    intro pos hni hnj; unfold Comparator.apply; rw [if_neg hni, if_neg hnj]
  rw [filter_decomp c, filter_decomp c]
  -- Complement parts are equal (c.apply w = w outside {c.i, c.j})
  have hcompl_eq : ((univ \ {c.i, c.j}).filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (c.apply w pos).val < k)) =
    ((univ \ {c.i, c.j}).filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (w pos).val < k)) := by
    ext pos; constructor <;> intro h
    all_goals {
      simp only [mem_filter, mem_sdiff, mem_univ, true_and] at h ⊢
      have hne := not_mem_pair_iff.mp h.1
      rw [hcompl pos hne.1 hne.2] at *; exact h }
  rw [hcompl_eq]; apply Nat.add_le_add_right
  -- Pair {c.i, c.j} analysis
  have hci : c.apply w c.i = min (w c.i) (w c.j) := by
    unfold Comparator.apply; rw [if_pos rfl]
  have hcj : c.apply w c.j = max (w c.i) (w c.j) := by
    unfold Comparator.apply; rw [if_neg hij.symm, if_pos rfl]
  rw [card_filter_pair hij, card_filter_pair hij]; simp only [hci, hcj]
  -- Resolve min/max by splitting on the comparison, then omega
  by_cases hle : w c.i ≤ w c.j
  · simp only [min_eq_left hle, max_eq_right hle]; split_ifs <;> omega
  · push_neg at hle
    simp only [min_eq_right hle.le, max_eq_left hle.le]
    have : c.i.val < c.j.val := c.h
    split_ifs <;> omega

/-! **Folding over comparator lists** -/

/-- Folding a list of comparators preserves the InitialHalved count bound. -/
theorem foldl_initialHalved_count_le {n : ℕ}
    (cs : List (Comparator n)) (w : Fin n → Fin n) (m k : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (cs.foldl (fun acc c ↦ c.apply acc) w pos).val < k)).card ≤
    (univ.filter (fun pos : Fin n ↦
      m ≤ pos.val ∧ (w pos).val < k)).card := by
  induction cs generalizing w with
  | nil => simp only [List.foldl_nil]; exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (comparator_initialHalved_count_le c w m k)

/-! **EpsilonInitialHalved is preserved by appending** -/

/-- Appending any comparator network preserves `EpsilonInitialHalved`. -/
theorem EpsilonInitialHalved_append {n : ℕ} {w : Fin n → Fin n} {ε : ℝ}
    (h : EpsilonInitialHalved w ε) (net : ComparatorNetwork n) :
    EpsilonInitialHalved (net.exec w) ε := by
  unfold EpsilonInitialHalved at h ⊢
  simp only [Fintype.card_fin, rank_fin_val] at h ⊢
  intro k hk
  calc ((univ.filter (fun pos : Fin n ↦
      n / 2 ≤ pos.val ∧ (net.exec w pos).val < k)).card : ℝ)
      ≤ (univ.filter (fun pos : Fin n ↦
          n / 2 ≤ pos.val ∧ (w pos).val < k)).card := by
        exact_mod_cast foldl_initialHalved_count_le net.comparators w (n / 2) k
    _ ≤ ε * k := h k hk

/-! **EpsilonFinalHalved via the dual** -/

/-- A single comparator can only decrease the count of positions in `{pos : pos.val < m}`
    with output value above threshold `2m - k`.

    This is the dual of `comparator_initialHalved_count_le`: the "bad" set
    `{pos : pos.val < m}` is downward-closed, and `c.i < c.j` ensures that
    if `c.j` is bad then `c.i` is too. Position `c.i` receives the min
    (smaller value), reducing its chance of exceeding the threshold. -/
theorem comparator_finalHalved_count_le {n : ℕ} (c : Comparator n)
    (w : Fin n → Fin n) (m k : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < m ∧ (c.apply w pos).val ≥ n - k)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < m ∧ (w pos).val ≥ n - k)).card := by
  have hij : c.i ≠ c.j := Fin.ne_of_lt c.h
  have hcompl : ∀ pos : Fin n, pos ≠ c.i → pos ≠ c.j → c.apply w pos = w pos := by
    intro pos hni hnj; unfold Comparator.apply; rw [if_neg hni, if_neg hnj]
  rw [filter_decomp c, filter_decomp c]
  have hcompl_eq : ((univ \ {c.i, c.j}).filter (fun pos : Fin n ↦
      pos.val < m ∧ (c.apply w pos).val ≥ n - k)) =
    ((univ \ {c.i, c.j}).filter (fun pos : Fin n ↦
      pos.val < m ∧ (w pos).val ≥ n - k)) := by
    ext pos; constructor <;> intro h
    all_goals {
      simp only [mem_filter, mem_sdiff, mem_univ, true_and] at h ⊢
      have hne := not_mem_pair_iff.mp h.1
      rw [hcompl pos hne.1 hne.2] at *; exact h }
  rw [hcompl_eq]; apply Nat.add_le_add_right
  have hci : c.apply w c.i = min (w c.i) (w c.j) := by
    unfold Comparator.apply; rw [if_pos rfl]
  have hcj : c.apply w c.j = max (w c.i) (w c.j) := by
    unfold Comparator.apply; rw [if_neg hij.symm, if_pos rfl]
  rw [card_filter_pair hij, card_filter_pair hij]; simp only [hci, hcj]
  by_cases hle : w c.i ≤ w c.j
  · simp only [min_eq_left hle, max_eq_right hle]; split_ifs <;> omega
  · push_neg at hle
    simp only [min_eq_right hle.le, max_eq_left hle.le]
    have : c.i.val < c.j.val := c.h
    split_ifs <;> omega

/-- Folding a list of comparators preserves the FinalHalved count bound. -/
theorem foldl_finalHalved_count_le {n : ℕ}
    (cs : List (Comparator n)) (w : Fin n → Fin n) (m k : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < m ∧ (cs.foldl (fun acc c ↦ c.apply acc) w pos).val ≥ n - k)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < m ∧ (w pos).val ≥ n - k)).card := by
  induction cs generalizing w with
  | nil => simp only [List.foldl_nil]; exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (comparator_finalHalved_count_le c w m k)

/-- Appending any comparator network preserves `EpsilonFinalHalved`. -/
theorem EpsilonFinalHalved_append {n : ℕ} {w : Fin n → Fin n} {ε : ℝ}
    (h : EpsilonFinalHalved w ε) (net : ComparatorNetwork n) :
    EpsilonFinalHalved (net.exec w) ε := by
  unfold EpsilonFinalHalved EpsilonInitialHalved at h ⊢
  simp only [Fintype.card_orderDual, Fintype.card_fin] at h ⊢
  intro k hk
  simp only [rank_fin_od, rank_fin_od_fin] at h ⊢
  -- Translate dual-rank conditions (n/2 ≤ n-1-pos.val, n-1-(f pos).val < k)
  -- to val-based conditions (pos.val < n-n/2, (f pos).val ≥ n-k)
  have filter_conv : ∀ (f : Fin n → Fin n),
      Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
        n / 2 ≤ n - 1 - pos.val ∧ n - 1 - (f pos).val < k) =
      Finset.univ.filter (fun pos : (Fin n)ᵒᵈ ↦
        pos.val < n - n / 2 ∧ (f pos).val ≥ n - k) := by
    intro f; ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := pos.isLt; have := (f pos).isLt
    constructor <;> intro ⟨ha, hb⟩ <;> constructor <;> omega
  rw [filter_conv (net.exec w)]
  have h' := h k hk; rw [filter_conv w] at h'
  change ((Finset.univ.filter (fun pos : Fin n ↦
    pos.val < n - n / 2 ∧ (net.exec w pos).val ≥ n - k)).card : ℝ) ≤ ε * ↑k
  simp only [ComparatorNetwork.exec] at *
  exact le_trans (by exact_mod_cast foldl_finalHalved_count_le net.comparators w (n - n / 2) k) h'

/-! **Combined results** -/

/-- Appending any comparator network preserves `EpsilonHalved`. -/
theorem EpsilonHalved_append {n : ℕ} {w : Fin n → Fin n} {ε : ℝ}
    (h : EpsilonHalved w ε) (net : ComparatorNetwork n) :
    EpsilonHalved (net.exec w) ε :=
  ⟨EpsilonInitialHalved_append h.1 net, EpsilonFinalHalved_append h.2 net⟩

/-- Appending any comparator network to an ε-halver yields an ε-halver. -/
theorem IsEpsilonHalver_append {n : ℕ} {net₁ : ComparatorNetwork n} {ε : ℝ}
    (h : IsEpsilonHalver net₁ ε) (net₂ : ComparatorNetwork n) :
    IsEpsilonHalver ⟨net₁.comparators ++ net₂.comparators⟩ ε := by
  intro v
  rw [ComparatorNetwork.exec_append]
  exact EpsilonHalved_append (h v) net₂

end


