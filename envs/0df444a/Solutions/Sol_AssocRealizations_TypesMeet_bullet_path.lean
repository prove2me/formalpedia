-- Prove2me | solution 1 for AssocRealizations.TypesMeet.bullet_path
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T12:44:44.970015+00:00
-- url     : https://prove2.me/submissions/641b838e-e51d-4bdb-b0d5-dadeb2c2d533

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
/-- an edge of a triangle whose endpoints have equal signs is a boundary edge -/
lemma Pd346_bdry {n : ℕ} (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hB : OppositeSignB σ T) (a b : Fin (n + 3)) (hE : IsEdge T s(a, b))
    (hs : hlSignPos σ a = hlSignPos σ b) : IsBoundaryEdge s(a, b) := by
  rcases hE with h | h
  · exact h
  · exact absurd hs (hB _ (Finset.mem_union_left _ h) a b rfl)

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
theorem solution (n : ℕ) (σ : Fin (n - 1) → Bool)
    (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T) (hB : OppositeSignB σ T) :
    ∀ t ∈ triangles (n + 3) T,
      ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
        IsBoundaryEdge s(a, b) ∧ hlSignPos σ a = hlSignPos σ b := by
  intro t ht
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    true_and] at ht
  obtain ⟨hcard, hedge⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hcard
  have hx : x ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have pick : ∀ a b : Fin (n + 3), a ∈ ({x, y, z} : Finset (Fin (n + 3))) →
      b ∈ ({x, y, z} : Finset (Fin (n + 3))) → a ≠ b → hlSignPos σ a = hlSignPos σ b →
      ∃ a ∈ ({x, y, z} : Finset (Fin (n + 3))), ∃ b ∈ ({x, y, z} : Finset (Fin (n + 3))),
        a ≠ b ∧ IsBoundaryEdge s(a, b) ∧ hlSignPos σ a = hlSignPos σ b :=
    fun a b ha hb hab hs => ⟨a, ha, b, hb, hab, Pd346_bdry σ T hB a b (hedge a ha b hb hab) hs, hs⟩
  rcases hsx : hlSignPos σ x <;> rcases hsy : hlSignPos σ y <;> rcases hsz : hlSignPos σ z
  · exact pick x y hx hy hxy (by rw [hsx, hsy])
  · exact pick x y hx hy hxy (by rw [hsx, hsy])
  · exact pick x z hx hz hxz (by rw [hsx, hsz])
  · exact pick y z hy hz hyz (by rw [hsy, hsz])
  · exact pick y z hy hz hyz (by rw [hsy, hsz])
  · exact pick x z hx hz hxz (by rw [hsx, hsz])
  · exact pick x y hx hy hxy (by rw [hsx, hsy])
  · exact pick x y hx hy hxy (by rw [hsx, hsy])
