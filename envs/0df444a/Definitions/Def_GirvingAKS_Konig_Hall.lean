-- Prove2me | Definitions.Def_GirvingAKS_Konig_Hall
-- name    : GirvingAKS_Konig_Hall
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:35.054698+00:00
-- url     : https://prove2.me/theorems/7b56bf21-e177-4655-8b4d-576c6dcd0407
-- title:
--   AKS sorting networks (Seiferas port) — Hall's Condition for Regular Bipartite Multigraphs
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Konig/Hall.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves Hall's marriage condition for d-regular bipartite multigraphs (with d > 0), then derives the existence of a perfect matching via Mathlib's Hall theorem.
--
--   Main results:
--
--   - `hall_condition`         — Hall's condition holds for `RegBipartite`
--   - `exists_perfect_matching` — every `RegBipartite` (d > 0) has a `PerfectMatching`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Konig/Hall.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Konig_Defs
import Mathlib.Combinatorics.Hall.Finite

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Konig/Hall.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Hall's Condition for Regular Bipartite Multigraphs

  Proves Hall's marriage condition for d-regular bipartite multigraphs
  (with d > 0), then derives the existence of a perfect matching via
  Mathlib's Hall theorem.

  Main results:
  • `hall_condition`         — Hall's condition holds for `RegBipartite`
  • `exists_perfect_matching` — every `RegBipartite` (d > 0) has a `PerfectMatching`
-/


section


open Finset BigOperators


/-! **Hall's Condition** -/

/-- Hall's condition for d-regular bipartite multigraphs (d > 0):
    for any set S of top vertices, |N(S)| ≥ |S|.

    Proof: S has d·|S| outgoing edge-slots. Each bottom vertex in N(S) absorbs
    at most d (by `bot_regular`). So d·|S| ≤ d·|N(S)|, hence |S| ≤ |N(S)|. -/
theorem RegBipartite.hall_condition {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d)
    (S : Finset (Fin m)) :
    S.card ≤ (S.biUnion (fun v ↦ univ.image (B.edges v))).card := by
  set N := S.biUnion (fun v ↦ univ.image (B.edges v))
  -- Step 1: d * |S| = number of edge-slots from S
  -- Each (v, p) with v ∈ S contributes one edge-slot
  have h_slots : d * S.card = (S ×ˢ (univ : Finset (Fin d))).card := by
    rw [card_product, card_univ, Fintype.card_fin, Nat.mul_comm]
  -- Step 2: Each edge-slot (v, p) from S lands in N
  have h_land : ∀ vp ∈ S ×ˢ (univ : Finset (Fin d)),
      B.edges vp.1 vp.2 ∈ N := by
    intro ⟨v, p⟩ hvp
    simp only [mem_product, mem_univ, and_true] at hvp
    exact mem_biUnion.mpr ⟨v, hvp, mem_image.mpr ⟨p, mem_univ _, rfl⟩⟩
  -- Step 3: For each u ∈ N, at most d edge-slots from S land on u
  -- (bot_regular gives exactly d from ALL of Fin m, so ≤ d from S ⊆ Fin m)
  have h_absorb : ∀ u ∈ N,
      ((S ×ˢ (univ : Finset (Fin d))).filter (fun vp ↦ B.edges vp.1 vp.2 = u)).card ≤ d := by
    intro u _
    calc ((S ×ˢ univ).filter (fun vp ↦ B.edges vp.1 vp.2 = u)).card
        ≤ ((univ ×ˢ univ).filter (fun vp : Fin m × Fin d ↦ B.edges vp.1 vp.2 = u)).card := by
          apply card_le_card (filter_subset_filter _ (product_subset_product_left (subset_univ S)))
      _ = d := B.bot_regular u
  -- Step 4: Combine via pigeonhole
  -- d * |S| = |S × [d]| = Σ_{u ∈ N} |fiber(u)| ≤ Σ_{u ∈ N} d = d * |N|
  suffices d * S.card ≤ d * N.card from Nat.le_of_mul_le_mul_left this hd
  rw [h_slots]
  calc (S ×ˢ univ).card
      = ((S ×ˢ univ).filter (fun vp ↦ B.edges vp.1 vp.2 ∈ N)).card := by
        congr 1; rw [filter_true_of_mem]; intro ⟨v, p⟩ hvp
        exact h_land ⟨v, p⟩ hvp
    _ ≤ ∑ u ∈ N, ((S ×ˢ univ).filter (fun vp ↦ B.edges vp.1 vp.2 = u)).card := by
        rw [← card_biUnion (fun u₁ _ u₂ _ hne ↦ by
          simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_product,
            mem_univ, and_true]
          intro ⟨v, p⟩ ⟨_, h₁⟩ ⟨_, h₂⟩; exact hne (h₁.symm.trans h₂))]
        apply card_le_card; intro ⟨v, p⟩ hvp
        simp only [mem_filter, mem_product, mem_univ, and_true] at hvp
        exact mem_biUnion.mpr ⟨B.edges v p, hvp.2, mem_filter.mpr ⟨mem_product.mpr ⟨hvp.1, mem_univ _⟩, rfl⟩⟩
    _ ≤ ∑ _u ∈ N, d := sum_le_sum h_absorb
    _ = N.card * d := by rw [sum_const, smul_eq_mul]
    _ = d * N.card := Nat.mul_comm _ _


/-! **Perfect Matching Existence** -/

/-- Every d-regular bipartite multigraph (d > 0) has a perfect matching.

    Applies Hall's marriage theorem (Mathlib) to `hall_condition`. -/
noncomputable def RegBipartite.exists_perfect_matching {m d : ℕ} (B : RegBipartite m d)
    (hd : 0 < d) : PerfectMatching B := by
  -- Hall's theorem gives f : Fin m → Fin m with f v ∈ image (B.edges v) for all v
  have hall := (all_card_le_biUnion_card_iff_existsInjective'
    (fun v : Fin m ↦ univ.image (B.edges v))).mp (B.hall_condition hd)
  choose f hf using hall
  obtain ⟨hf_inj, hf_mem⟩ := hf
  -- f v ∈ image (B.edges v) means ∃ p, B.edges v p = f v
  have hport : ∀ v, ∃ p : Fin d, B.edges v p = f v := by
    intro v; obtain ⟨p, _, hp⟩ := mem_image.mp (hf_mem v); exact ⟨p, hp⟩
  exact ⟨fun v ↦ (hport v).choose, fun v₁ v₂ h ↦ by
    have h₁ := (hport v₁).choose_spec
    have h₂ := (hport v₂).choose_spec
    exact hf_inj (h₁.symm.trans (h.trans h₂))⟩

end


