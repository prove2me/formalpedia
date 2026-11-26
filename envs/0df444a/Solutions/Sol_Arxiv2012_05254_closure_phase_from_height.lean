-- Prove2me | solution 1 for Arxiv2012_05254.closure_phase_from_height
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:04:24.83916+00:00
-- url     : https://prove2.me/submissions/bb103f0b-8d7f-4d1e-b9d4-65e2b574ac10

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S70NT
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

lemma exists_t (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (ζ : Fin 3 → ℝ) :
    ∃ t : Plane, ∀ a b, ⟪x b - x a, t⟫ = ζ b - ζ a := by
  classical
  have hspan : affineSpan ℝ (Set.range x) = ⊤ := by
    rw [hx.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  let bs : AffineBasis (Fin 3) ℝ Plane := ⟨x, hx, hspan⟩
  have hb : ∀ a, bs a = x a := fun a => rfl
  let φ : Plane →ᵃ[ℝ] ℝ := ζ 0 • bs.coord 0 + ζ 1 • bs.coord 1 + ζ 2 • bs.coord 2
  have hφ : ∀ c, φ (x c) = ζ c := by
    intro c
    simp only [φ, AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ← hb, AffineBasis.coord_apply]
    fin_cases c <;> simp
  refine ⟨(InnerProductSpace.toDual ℝ Plane).symm (LinearMap.toContinuousLinearMap φ.linear),
    fun a b => ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap']
  rw [show x b - x a = x b -ᵥ x a from rfl, AffineMap.linearMap_vsub, hφ, hφ, vsub_eq_sub]

lemma core (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (ψ c : Fin 3 → ℝ) :
    ((∃ t : Plane, npcTranslate x ψ (ψ + c) t) →
      ∃ ξ : Fin 3 → ℝ, ∀ a, c a = ξ (a + 1) - ξ a) ∧
    ((∃ ξ : Fin 3 → ℝ, ∀ a, c a = ξ (a + 1) - ξ a) → c 0 + c 1 + c 2 = 0) ∧
    (c 0 + c 1 + c 2 = 0 → ∃ t : Plane, npcTranslate x ψ (ψ + c) t) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun a => -(2 * Real.pi * ⟪x a, t⟫), fun a => ?_⟩
    have h := ht a
    rw [npc_shift] at h
    have := npc_inj _ (spacing_ne x hx a) _ _ h
    simp only [Pi.add_apply, spacing, inner_sub_left] at this
    linarith
  · rintro ⟨ξ, hξ⟩
    rw [hξ 0, hξ 1, hξ 2]
    have h1 : (0 : Fin 3) + 1 = 1 := rfl
    have h2 : (1 : Fin 3) + 1 = 2 := rfl
    have h3 : (2 : Fin 3) + 1 = 0 := rfl
    rw [h1, h2, h3]; ring
  · intro hsum
    obtain ⟨t, ht⟩ := exists_t x hx ![0, -(c 0) / (2 * Real.pi), -(c 0 + c 1) / (2 * Real.pi)]
    refine ⟨t, fun a => ?_⟩
    rw [npc_shift]
    congr 1
    simp only [Pi.add_apply, spacing]
    rw [real_inner_comm, ← real_inner_comm, ht]
    have hπ := Real.pi_ne_zero
    fin_cases a
    · simp; field_simp; ring
    · simp; field_simp; ring
    · simp; field_simp; linarith

end S70NT

open Arxiv2012_05254 S70NT in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (a : Fin 3) :
    (∃ V : Plane, V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2))) ∧
    ∀ V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2)),
      recentredPhase (spacing x (a + 1)) (ψ (a + 1)) V = 0 ∧
      recentredPhase (spacing x (a + 2)) (ψ (a + 2)) V = 0 ∧
      closurePhase ψ = recentredPhase (spacing x a) (ψ a) V ∧
      |closurePhase ψ| =
        2 * Real.pi * ‖spacing x a‖ * Metric.infDist V (npc (spacing x a) (ψ a)) := by
  have f1 : a + 1 + 1 = a + 2 := by fin_cases a <;> decide
  have f2 : a + 2 + 1 = a := by fin_cases a <;> decide
  have f3 : a + 2 ≠ a + 1 := by fin_cases a <;> decide
  have f4 : a ≠ a + 1 := by fin_cases a <;> decide
  have f5 : a ≠ a + 2 := by fin_cases a <;> decide
  have hπ := Real.pi_pos
  have hcp : closurePhase ψ = ψ a + ψ (a + 1) + ψ (a + 2) := by
    unfold closurePhase; rw [Fin.sum_univ_three]; fin_cases a <;> simp <;> ring
  have hsum : spacing x a = -(spacing x (a + 1) + spacing x (a + 2)) := by
    unfold spacing; rw [f1, f2]; abel
  refine ⟨?_, fun V hV => ?_⟩
  · let ζ : Fin 3 → ℝ := fun b => if b = a + 1 then 0 else if b = a + 2 then -(ψ (a + 1)) / (2 * Real.pi)
      else -(ψ (a + 1) + ψ (a + 2)) / (2 * Real.pi)
    obtain ⟨V, hV⟩ := exists_t x hx ζ
    refine ⟨V, ?_, ?_⟩
    · show 2 * Real.pi * ⟪spacing x (a + 1), V⟫ + ψ (a + 1) = 0
      unfold spacing; rw [hV, f1]
      simp only [ζ, f3, if_true, if_false]
      field_simp; ring
    · show 2 * Real.pi * ⟪spacing x (a + 2), V⟫ + ψ (a + 2) = 0
      unfold spacing; rw [hV, f2]
      simp only [ζ, f3, f4, f5, if_true, if_false]
      field_simp; ring
  · obtain ⟨h1, h2⟩ := hV
    have h1' : 2 * Real.pi * ⟪spacing x (a + 1), V⟫ + ψ (a + 1) = 0 := h1
    have h2' : 2 * Real.pi * ⟪spacing x (a + 2), V⟫ + ψ (a + 2) = 0 := h2
    have hk : recentredPhase (spacing x a) (ψ a) V = closurePhase ψ := by
      unfold recentredPhase; rw [hcp, hsum, inner_neg_left, inner_add_left]; linarith
    refine ⟨by unfold recentredPhase; linarith, by unfold recentredPhase; linarith, hk.symm, ?_⟩
    set u := spacing x a
    set k := closurePhase ψ
    have hu : u ≠ 0 := spacing_ne x hx a
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hk' : ψ a + 2 * Real.pi * ⟪u, V⟫ = k := hk
    -- distance
    have hd : Metric.infDist V (npc u (ψ a)) = |k| / (2 * Real.pi * ‖u‖) := by
      set P : Plane := V - (k / (2 * Real.pi * ‖u‖ ^ 2)) • u
      have hP : P ∈ npc u (ψ a) := by
        show 2 * Real.pi * ⟪u, P⟫ + ψ a = 0
        simp only [P, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp; linarith
      have hdP : dist V P = |k| / (2 * Real.pi * ‖u‖) := by
        simp only [P, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div,
          abs_of_pos (by positivity : 0 < 2 * Real.pi * ‖u‖ ^ 2)]
        field_simp
      apply le_antisymm
      · rw [← hdP]; exact Metric.infDist_le_dist_of_mem hP
      · rw [Metric.le_infDist ⟨P, hP⟩]
        intro s hs
        have hs' : 2 * Real.pi * ⟪u, s⟫ + ψ a = 0 := hs
        have e : |k| = 2 * Real.pi * |⟪u, V - s⟫| := by
          have : k = 2 * Real.pi * (⟪u, V⟫ - ⟪u, s⟫) := by linarith
          rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), inner_sub_right]
        have cs := abs_real_inner_le_norm u (V - s)
        rw [div_le_iff₀ (by positivity), e, dist_eq_norm]
        nlinarith
    rw [hd]; field_simp
