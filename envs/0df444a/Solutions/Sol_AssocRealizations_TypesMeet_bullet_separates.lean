-- Prove2me | solution 1 for AssocRealizations.TypesMeet.bullet_separates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T12:38:19.510793+00:00
-- url     : https://prove2.me/submissions/dd3bab2d-940f-4947-b94f-26332650cbdc

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

set_option autoImplicit false

open ChvatalArtGallery.FanPartition

namespace P04cf

open AssocRealizations.TypesMeet

lemma cdist_eq_sub {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c = (c - a).val := by
  unfold cdist
  rw [Fin.sub_def]
  simp only
  congr 1
  have := a.isLt
  omega

lemma cdist_lt {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c < N := by
  rw [cdist_eq_sub]; exact (c - a).isLt

lemma cdist_eq_zero {N : ℕ} [NeZero N] (a c : Fin N) : cdist a c = 0 ↔ a = c := by
  rw [cdist_eq_sub, Fin.val_eq_zero_iff, sub_eq_zero, eq_comm]

lemma cdist_swap {N : ℕ} [NeZero N] (a c : Fin N) (h : a ≠ c) :
    cdist c a = N - cdist a c := by
  rw [cdist_eq_sub, cdist_eq_sub]
  have h1 : a - c = -(c - a) := by abel
  rw [h1, Fin.coe_neg]
  have h2 : (c - a).val ≠ 0 := by
    intro h0
    rw [Fin.val_eq_zero_iff, sub_eq_zero] at h0
    exact h h0.symm
  have h3 := (c - a).isLt
  rw [Nat.mod_eq_of_lt (by omega)]


lemma cdist_inj {N : ℕ} [NeZero N] (a x y : Fin N) (h : cdist a x = cdist a y) : x = y := by
  rw [cdist_eq_sub, cdist_eq_sub] at h
  exact sub_left_injective (Fin.ext h)

lemma cdist_via {N : ℕ} [NeZero N] (o a x : Fin N) :
    cdist a x = if cdist o a ≤ cdist o x then cdist o x - cdist o a
      else cdist o x + N - cdist o a := by
  rw [cdist_eq_sub, cdist_eq_sub, cdist_eq_sub]
  have h1 : x - a = (x - o) - (a - o) := by abel
  rw [h1]
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 (Fin.le_iff_val_le_val.2 h)
  · have hlt : x - o < a - o := Fin.lt_iff_val_lt_val.2 (by omega)
    rw [Fin.coe_sub_iff_lt.2 hlt]
    omega


lemma bdry_pos {N : ℕ} [NeZero N] (u v : Fin N) (h : IsBoundaryEdge s(u, v)) :
    cdist u v = 1 ∨ cdist v u = 1 := by
  obtain ⟨a, b, hab, h1⟩ := h
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- three pairwise adjacent vertices force a triangle -/
lemma three_adj {N : ℕ} [NeZero N] (x y z : Fin N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (b1 : IsBoundaryEdge s(x, y)) (b2 : IsBoundaryEdge s(x, z)) (b3 : IsBoundaryEdge s(y, z)) :
    N = 3 := by
  have e1 := bdry_pos x y b1
  have e2 := bdry_pos x z b2
  have e3 := bdry_pos y z b3
  rw [cdist_swap x y hxy] at e1
  rw [cdist_swap x z hxz] at e2
  rw [cdist_swap y z hyz] at e3
  have ly := cdist_lt x y
  have lz := cdist_lt x z
  have hy0 : cdist x y ≠ 0 := fun h => hxy ((cdist_eq_zero x y).1 h)
  have hz0 : cdist x z ≠ 0 := fun h => hxz ((cdist_eq_zero x z).1 h)
  have hyz' : cdist x y ≠ cdist x z := fun h => hyz (cdist_inj x y z h)
  have v := cdist_via x y z
  split_ifs at v <;> omega

lemma sign_n0 (σ : Fin (0 - 1) → Bool) :
    hlSignPos σ (0 : Fin 3) = false ∧ hlSignPos σ (1 : Fin 3) = true := by
  revert σ; decide

end P04cf

open ChvatalArtGallery.FanPartition AssocRealizations.TypesMeet in
lemma P04cf_bdry {n : ℕ} (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
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
      ¬ ∃ sign : Bool, ∀ p ∈ t, hlSignPos σ p = sign := by
  intro t ht ⟨sg, hsg⟩
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    true_and] at ht
  obtain ⟨hcard, hedge⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hcard
  have hx : x ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have hz : z ∈ ({x, y, z} : Finset (Fin (n + 3))) := by simp
  have bd : ∀ a b : Fin (n + 3), a ∈ ({x, y, z} : Finset (Fin (n + 3))) →
      b ∈ ({x, y, z} : Finset (Fin (n + 3))) → a ≠ b → IsBoundaryEdge s(a, b) :=
    fun a b ha hb hab => P04cf_bdry σ T hB a b (hedge a ha b hb hab)
      ((hsg a ha).trans (hsg b hb).symm)
  have hN : n + 3 = 3 := P04cf.three_adj x y z hxy hxz hyz (bd x y hx hy hxy)
    (bd x z hx hz hxz) (bd y z hy hz hyz)
  have hn : n = 0 := by omega
  subst hn
  have huniv : ({x, y, z} : Finset (Fin (0 + 3))) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard]; rfl)
  have h0 := hsg 0 (by rw [huniv]; exact Finset.mem_univ _)
  have h1 := hsg 1 (by rw [huniv]; exact Finset.mem_univ _)
  have := P04cf.sign_n0 σ
  rw [this.1] at h0
  rw [this.2] at h1
  rw [← h0] at h1
  exact Bool.noConfusion h1
