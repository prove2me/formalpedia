-- Prove2me | solution 1 for Arxiv2012_05254.complementary_triangles_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:45:15.238898+00:00
-- url     : https://prove2.me/submissions/945e7746-4700-499e-a121-e77743a01598

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S78CT
open Arxiv2012_05254

lemma npc_shift (u : Plane) (α : ℝ) (t : Plane) :
    (fun s => s + t) '' npc u α = npc u (α - 2 * Real.pi * ⟪u, t⟫) := by
  ext s
  simp only [npc, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s0, h, rfl⟩
    rw [inner_add_right]; linarith
  · intro h
    exact ⟨s - t, by rw [inner_sub_right]; linarith, sub_add_cancel s t⟩

lemma npc_inj (u : Plane) (hu : u ≠ 0) (α β : ℝ) (h : npc u α = npc u β) : α = β := by
  have hn : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu
  have hπ := Real.pi_pos
  set s : Plane := (-α / (2 * Real.pi * ⟪u, u⟫)) • u with hs_def
  have hs2 : 2 * Real.pi * ⟪u, s⟫ = -α := by
    rw [hs_def, inner_smul_right]; field_simp
  have hs : s ∈ npc u α := by
    show 2 * Real.pi * ⟪u, s⟫ + α = 0
    linarith
  rw [h] at hs
  have : 2 * Real.pi * ⟪u, s⟫ + β = 0 := hs
  linarith

lemma spacing_ne (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (a : Fin 3) :
    spacing x a ≠ 0 := by
  unfold spacing
  intro h
  have := hx.injective (sub_eq_zero.1 h)
  fin_cases a <;> simp at this

lemma proj_mem (u : Plane) (hu : u ≠ 0) (s : Plane) (β : ℝ) :
    s - ((2 * Real.pi * ⟪u, s⟫ + β) / (2 * Real.pi * ‖u‖ ^ 2)) • u ∈ npc u β := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hπ := Real.pi_pos
  show 2 * Real.pi * ⟪u, _⟫ + β = 0
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp; ring

lemma infDist_npc (u : Plane) (hu : u ≠ 0) (s : Plane) (β : ℝ) :
    2 * Real.pi * ‖u‖ * Metric.infDist s (npc u β) = |2 * Real.pi * ⟪u, s⟫ + β| := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hπ := Real.pi_pos
  have hc : 0 < 2 * Real.pi * ‖u‖ := by positivity
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := s) (proj_mem u hu s β)
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_pos (show 0 < 2 * Real.pi * ‖u‖ ^ 2 by positivity)] at h
    calc 2 * Real.pi * ‖u‖ * Metric.infDist s (npc u β)
        ≤ 2 * Real.pi * ‖u‖ * (|2 * Real.pi * ⟪u, s⟫ + β| / (2 * Real.pi * ‖u‖ ^ 2) * ‖u‖) :=
          mul_le_mul_of_nonneg_left h hc.le
      _ = _ := by field_simp
  · rw [← div_le_iff₀' hc, Metric.le_infDist ⟨_, proj_mem u hu s β⟩]
    intro y hy
    have hy' : 2 * Real.pi * ⟪u, y⟫ + β = 0 := hy
    rw [div_le_iff₀' hc, dist_eq_norm]
    have : 2 * Real.pi * ⟪u, s⟫ + β = 2 * Real.pi * ⟪u, s - y⟫ := by
      rw [inner_sub_right]; linarith
    rw [this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), mul_assoc]
    have hcs := abs_real_inner_le_norm u (s - y)
    nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

lemma key (x : Fin 3 → Plane) (ψ : Fin 3 → ℝ) (a : Fin 3) (V : Plane)
    (hV : V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2))) :
    2 * Real.pi * ⟪spacing x a, V⟫ + ψ a = closurePhase ψ := by
  obtain ⟨h1, h2⟩ := hV
  have h1' : 2 * Real.pi * ⟪spacing x (a + 1), V⟫ + ψ (a + 1) = 0 := h1
  have h2' : 2 * Real.pi * ⟪spacing x (a + 2), V⟫ + ψ (a + 2) = 0 := h2
  have hs : spacing x a + spacing x (a + 1) + spacing x (a + 2) = 0 := by
    simp only [spacing]
    have : a + 2 + 1 = a := by fin_cases a <;> rfl
    have h' : a + 1 + 1 = a + 2 := by fin_cases a <;> rfl
    rw [this, h']; abel
  have hsum : closurePhase ψ = ψ a + ψ (a + 1) + ψ (a + 2) := by
    simp only [closurePhase, Fin.sum_univ_three]
    fin_cases a <;> simp <;> ring
  have hi : ⟪spacing x a, V⟫ = -⟪spacing x (a + 1), V⟫ - ⟪spacing x (a + 2), V⟫ := by
    rw [show spacing x a = -spacing x (a + 1) - spacing x (a + 2) by
      rw [← sub_eq_zero, ← hs]; abel]
    rw [inner_sub_left, inner_neg_left]
  rw [hsum, hi]; linarith

end S78CT

open Arxiv2012_05254 in
open scoped RealInnerProductSpace in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (a : Fin 3) (V : Plane)
    (hV : V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2))) :
    (∃ n : ℤ, V ∈ convexHull ℝ (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ)) ∪
        npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1)))) ∧
    ∀ n : ℤ, V ∈ convexHull ℝ (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ)) ∪
        npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1))) →
      2 * Real.pi * ‖spacing x a‖ *
          Metric.infDist V (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ))) =
        |closurePhase ψ + 2 * Real.pi * (n : ℝ)| ∧
      2 * Real.pi * ‖spacing x a‖ *
          Metric.infDist V (npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1))) =
        |closurePhase ψ + 2 * Real.pi * ((n : ℝ) + 1)| ∧
      |closurePhase ψ + 2 * Real.pi * (n : ℝ)| + |closurePhase ψ + 2 * Real.pi * ((n : ℝ) + 1)| =
        2 * Real.pi := by
  set u := spacing x a with hu_def
  have hu : u ≠ 0 := S78CT.spacing_ne x hx a
  have hk := S78CT.key x ψ a V hV
  rw [← hu_def] at hk
  set c := closurePhase ψ with hc
  have hπ := Real.pi_pos
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  refine ⟨?_, fun n hmem => ⟨?_, ?_, ?_⟩⟩
  · refine ⟨⌊-c / (2 * Real.pi)⌋, ?_⟩
    set n : ℤ := ⌊-c / (2 * Real.pi)⌋
    have f1 : (n : ℝ) ≤ -c / (2 * Real.pi) := Int.floor_le _
    have f2 : -c / (2 * Real.pi) < n + 1 := Int.lt_floor_add_one _
    have g1 : c + 2 * Real.pi * n ≤ 0 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 f1; linarith
    have g2 : 0 < c + 2 * Real.pi * (n + 1) := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 f2; linarith
    set D := 2 * Real.pi * ‖u‖ ^ 2 with hD
    have hDp : 0 < D := by positivity
    set k1 := (2 * Real.pi * ⟪u, V⟫ + (ψ a + 2 * Real.pi * n)) / D
    set k2 := (2 * Real.pi * ⟪u, V⟫ + (ψ a + 2 * Real.pi * (n + 1))) / D
    have hk1 : k1 = (c + 2 * Real.pi * n) / D := by simp only [k1]; congr 1; linarith
    have hk2 : k2 = (c + 2 * Real.pi * (n + 1)) / D := by simp only [k2]; congr 1; linarith
    have hk1n : k1 ≤ 0 := by rw [hk1]; exact div_nonpos_of_nonpos_of_nonneg g1 hDp.le
    have hk2p : 0 < k2 := by rw [hk2]; exact div_pos g2 hDp
    have m1 := S78CT.proj_mem u hu V (ψ a + 2 * Real.pi * (n : ℝ))
    have m2 := S78CT.proj_mem u hu V (ψ a + 2 * Real.pi * ((n : ℝ) + 1))
    refine segment_subset_convexHull (Set.mem_union_left _ m1) (Set.mem_union_right _ m2) ?_
    have hne' : k2 - k1 ≠ 0 := by linarith
    refine ⟨k2 / (k2 - k1), -k1 / (k2 - k1), div_nonneg hk2p.le (by linarith),
      div_nonneg (by linarith) (by linarith),
      by rw [← add_div, show k2 + -k1 = k2 - k1 by ring, div_self hne'], ?_⟩
    rw [smul_sub, smul_sub, smul_smul, smul_smul]
    have hne : k2 - k1 ≠ 0 := by linarith
    have e : k2 / (k2 - k1) * k1 + -k1 / (k2 - k1) * k2 = 0 := by field_simp; ring
    have e2 : k2 / (k2 - k1) + -k1 / (k2 - k1) = 1 := by field_simp; ring
    calc (k2 / (k2 - k1)) • V - (k2 / (k2 - k1) * k1) • u + ((-k1 / (k2 - k1)) • V - (-k1 / (k2 - k1) * k2) • u)
        = (k2 / (k2 - k1) + -k1 / (k2 - k1)) • V - (k2 / (k2 - k1) * k1 + -k1 / (k2 - k1) * k2) • u := by
          rw [add_smul, add_smul]; abel
      _ = V := by rw [e, e2, one_smul, zero_smul, sub_zero]
  · rw [S78CT.infDist_npc u hu]; congr 1; linarith
  · rw [S78CT.infDist_npc u hu]; congr 1; linarith
  · have hsub : convexHull ℝ (npc u (ψ a + 2 * Real.pi * (n : ℝ)) ∪
        npc u (ψ a + 2 * Real.pi * ((n : ℝ) + 1))) ⊆
        {s | -(2 * Real.pi * ((n : ℝ) + 1)) ≤ 2 * Real.pi * ⟪u, s⟫ + ψ a ∧
          2 * Real.pi * ⟪u, s⟫ + ψ a ≤ -(2 * Real.pi * (n : ℝ))} := by
      apply convexHull_min
      · rintro s (hs | hs)
        · have : 2 * Real.pi * ⟪u, s⟫ + (ψ a + 2 * Real.pi * (n : ℝ)) = 0 := hs
          constructor <;> nlinarith
        · have : 2 * Real.pi * ⟪u, s⟫ + (ψ a + 2 * Real.pi * ((n : ℝ) + 1)) = 0 := hs
          constructor <;> nlinarith
      · intro s hs t ht p q hp hq hpq
        simp only [Set.mem_setOf_eq, inner_add_right, inner_smul_right] at *
        have e : 2 * Real.pi * (p * ⟪u, s⟫ + q * ⟪u, t⟫) + ψ a =
            p * (2 * Real.pi * ⟪u, s⟫ + ψ a) + q * (2 * Real.pi * ⟪u, t⟫ + ψ a) := by
          linear_combination (-ψ a) * hpq
        rw [e]
        constructor
        · have i1 := mul_le_mul_of_nonneg_left hs.1 hp
          have i2 := mul_le_mul_of_nonneg_left ht.1 hq
          have kk : p * (-(2 * Real.pi * ((n : ℝ) + 1))) + q * (-(2 * Real.pi * ((n : ℝ) + 1))) =
              -(2 * Real.pi * ((n : ℝ) + 1)) := by rw [← add_mul, hpq, one_mul]
          linarith
        · have i1 := mul_le_mul_of_nonneg_left hs.2 hp
          have i2 := mul_le_mul_of_nonneg_left ht.2 hq
          have kk : p * (-(2 * Real.pi * (n : ℝ))) + q * (-(2 * Real.pi * (n : ℝ))) =
              -(2 * Real.pi * (n : ℝ)) := by rw [← add_mul, hpq, one_mul]
          linarith
    have h := hsub hmem
    simp only [Set.mem_setOf_eq] at h
    rw [hk] at h
    rw [abs_of_nonpos (by linarith [h.2]), abs_of_nonneg (by linarith [h.1])]
    ring
