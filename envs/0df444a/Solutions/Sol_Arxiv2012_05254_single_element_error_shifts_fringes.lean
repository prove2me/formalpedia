-- Prove2me | solution 1 for Arxiv2012_05254.single_element_error_shifts_fringes
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:03:07.901057+00:00
-- url     : https://prove2.me/submissions/656a616a-46a1-4020-ab55-d86edd26cf25

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

namespace S72SE
open Arxiv2012_05254 S70NT

lemma gen (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (ψ ξ : Fin 3 → ℝ) :
    ∃ t : Plane, (∀ a b, ⟪x b - x a, t⟫ = -(ξ b) / (2 * Real.pi) - -(ξ a) / (2 * Real.pi)) ∧
      npcTranslate x ψ (elementCorrupt ξ ψ) t := by
  obtain ⟨t, ht⟩ := exists_t x hx (fun a => -(ξ a) / (2 * Real.pi))
  refine ⟨t, ht, fun a => ?_⟩
  rw [npc_shift]
  congr 1
  simp only [elementCorrupt, spacing]
  rw [ht]
  have hπ := Real.pi_ne_zero
  field_simp
  ring

end S72SE

namespace S72SF
open Arxiv2012_05254 S70NT

lemma shiftw (u : Plane) (hu : u ≠ 0) (α d : ℝ) :
    ∃ w : Plane, (∃ c : ℝ, w = c • u) ∧ ‖w‖ = |d| / (2 * Real.pi * ‖u‖) ∧
      npc u (α + d) = (fun s => s + w) '' npc u α := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hπ := Real.pi_pos
  refine ⟨(-d / (2 * Real.pi * ‖u‖ ^ 2)) • u, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi * ‖u‖ ^ 2)]
    field_simp
  · rw [npc_shift, inner_smul_right, real_inner_self_eq_norm_sq]
    congr 1
    field_simp
    ring

end S72SF

open Arxiv2012_05254 S70NT S72SE S72SF in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (e : Fin 3) (δ : ℝ) :
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ (e + 1) = ψ (e + 1) ∧
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ e = ψ e - δ ∧
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ (e + 2) = ψ (e + 2) + δ ∧
    (∀ a ∈ ({e, e + 2} : Finset (Fin 3)), ∃ w : Plane, (∃ c : ℝ, w = c • spacing x a) ∧
      ‖w‖ = |δ| / (2 * Real.pi * ‖spacing x a‖) ∧
      npc (spacing x a) (elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ a) =
        (fun s => s + w) '' npc (spacing x a) (ψ a)) ∧
    ∃ t : Plane, npcTranslate x ψ (elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ) t := by
  have h1 : e + 1 + 1 ≠ e := by fin_cases e <;> decide
  have h2 : e + 1 ≠ e := by fin_cases e <;> decide
  have h3 : e + 2 + 1 = e := by fin_cases e <;> decide
  have h4 : e + 2 ≠ e := by fin_cases e <;> decide
  have A : elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ e = ψ e - δ := by
    simp [elementCorrupt, h2]
  have B : elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ (e + 2) = ψ (e + 2) + δ := by
    simp only [elementCorrupt, h3]; simp [h4]
  refine ⟨by simp [elementCorrupt, h1, h2], A, B, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · obtain ⟨w, hw1, hw2, hw3⟩ := shiftw (spacing x a) (spacing_ne x hx a) (ψ a) (-δ)
      refine ⟨w, hw1, by rw [hw2, abs_neg], ?_⟩
      rw [A, ← hw3]; ring_nf
    · obtain ⟨w, hw1, hw2, hw3⟩ := shiftw (spacing x (e + 2)) (spacing_ne x hx _) (ψ (e + 2)) δ
      exact ⟨w, hw1, hw2, by rw [B, hw3]⟩
  · obtain ⟨t, _, htr⟩ := gen x hx ψ (Pi.single e δ)
    exact ⟨t, htr⟩
