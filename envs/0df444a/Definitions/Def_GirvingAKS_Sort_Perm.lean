-- Prove2me | Definitions.Def_GirvingAKS_Sort_Perm
-- name    : GirvingAKS_Sort_Perm
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:51.964654+00:00
-- url     : https://prove2.me/theorems/5b9787ff-5e4f-4ad6-b4a9-15d9e0a67a6a
-- title:
--   AKS sorting networks (Seiferas port) — Permutation Principle for Sorting Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Perm.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** A comparator network sorts all inputs if and only if it sorts all permutations of `Fin n`.  This reduces the universal quantifier over arbitrary linear orders to the concrete type `Fin n`.
--
--   Proof: given `v : Fin n → α`, factor `v = g ∘ σ` where `σ` is a sorting permutation and `g = v ∘ σ⁻¹` is monotone.  Then `net.exec v = g ∘ net.exec σ` by `exec_comp_mono`, and the composition of two monotone functions is monotone.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Perm.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Monotone

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Perm.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Permutation Principle for Sorting Networks

  A comparator network sorts all inputs if and only if it sorts all
  permutations of `Fin n`.  This reduces the universal quantifier over
  arbitrary linear orders to the concrete type `Fin n`.

  Proof: given `v : Fin n → α`, factor `v = g ∘ σ` where `σ` is a sorting
  permutation and `g = v ∘ σ⁻¹` is monotone.  Then
  `net.exec v = g ∘ net.exec σ` by `exec_comp_mono`, and the composition
  of two monotone functions is monotone.
-/


section

/-- For any `v : Fin n → α`, there exists a permutation `σ` such that
    `v ∘ σ.symm` is monotone (i.e., `σ.symm` enumerates indices in
    non-decreasing value order). -/
theorem exists_sorting_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (v : Fin n → α) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (v ∘ ⇑σ.symm) := by
  -- Lex comparison on Fin n: (v a, a) ≤ (v b, b)
  let le := fun (a b : Fin n) => v a < v b ∨ (v a = v b ∧ a ≤ b)
  have hTrans : IsTrans (Fin n) le := ⟨fun {a b c} hab hbc => by
    rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
    · left; exact lt_trans h1 h3
    · left; rwa [← h3]
    · left; rwa [h1]
    · right; exact ⟨h1.trans h3, Fin.le_trans h2 h4⟩⟩
  have hAnti : Std.Antisymm le := ⟨fun {a b} hab hba => by
    rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hba with h3 | ⟨h3, h4⟩
    · exact absurd h1 (not_lt_of_gt h3)
    · exact absurd h1 (by rw [h3]; exact lt_irrefl _)
    · exact absurd h3 (by rw [h1]; exact lt_irrefl _)
    · exact le_antisymm h2 h4⟩
  have hTotal : Std.Total le := ⟨fun a b => by
    rcases lt_trichotomy (v a) (v b) with h | h | h
    · left; left; exact h
    · rcases le_total a b with hab | hab
      · left; right; exact ⟨h, hab⟩
      · right; right; exact ⟨h.symm, hab⟩
    · right; left; exact h⟩
  -- Sort Fin n by this comparison
  set L := (Finset.univ : Finset (Fin n)).sort le
  have hlen : L.length = n := by
    rw [Finset.length_sort, Finset.card_univ, Fintype.card_fin]
  have hnodup := Finset.sort_nodup Finset.univ le
  have hpw := Finset.pairwise_sort Finset.univ le
  -- f(i) = L[i]: the i-th element in sorted order
  let f : Fin n → Fin n := fun i => L.get (i.cast hlen.symm)
  have f_inj : Function.Injective f := by
    intro a b hab
    have h := hnodup.get_inj_iff.mp hab
    exact Fin.ext (by
      have h1 : (Fin.cast hlen.symm a).val = a.val := rfl
      have h2 : (Fin.cast hlen.symm b).val = b.val := rfl
      rw [← h1, ← h2, h])
  -- σ.symm = f (sorted lookup), σ = f⁻¹ (position in sorted list)
  let e := Equiv.ofBijective f (f_inj.bijective_of_finite)
  use e.symm
  -- Goal: Monotone (v ∘ e.symm.symm) = Monotone (v ∘ e) = Monotone (v ∘ f)
  show Monotone (v ∘ ⇑e)
  intro i j hij
  show v (e i) ≤ v (e j)
  change v (f i) ≤ v (f j)
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · -- L is pairwise sorted, so le (L[i]) (L[j]) for i < j
    have hle_ij := (List.pairwise_iff_getElem.mp hpw) i.val j.val
      (by rw [hlen]; exact i.isLt) (by rw [hlen]; exact j.isLt) hlt
    change v L[i.val] ≤ v L[j.val]
    rcases hle_ij with h | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h

/-- **Permutation principle**: a comparator network sorts all inputs if
    it sorts all permutations of `Fin n`.

    Stronger than the zero-one principle when the proof naturally works
    with rank permutations (e.g., the Seiferas bag-tree argument). -/
theorem perm_principle {n : ℕ} (net : ComparatorNetwork n) :
    (∀ σ : Equiv.Perm (Fin n), Monotone (net.exec σ)) → net.Sorts := by
  intro h α _ v
  obtain ⟨σ, hg_mono⟩ := exists_sorting_perm v
  -- v = g ∘ σ where g = v ∘ σ⁻¹ is monotone
  have hv : v = (v ∘ ⇑σ.symm) ∘ σ := by
    ext i; simp [Function.comp, Equiv.symm_apply_apply]
  rw [hv, net.exec_comp_mono hg_mono σ]
  exact hg_mono.comp (h σ)

end


