-- Prove2me | solution 1 for Arxiv2012_05254.sos_conservation_principle
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:40:07.407194+00:00
-- url     : https://prove2.me/submissions/fea46b43-9a56-4088-9e43-bfc717f58da7

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S70SOS
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

end S70SOS

open Arxiv2012_05254 in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ ξ : Fin 3 → ℝ) :
    (∃ t : Plane, npcTranslate x ψ (elementCorrupt ξ ψ) t ∧
      npcVertices x (elementCorrupt ξ ψ) = (fun s => s + t) '' npcVertices x ψ) ∧
    closurePhase (elementCorrupt ξ ψ) = closurePhase ψ ∧
    imageArea x (elementCorrupt ξ ψ) = imageArea x ψ := by
  set c : Fin 3 → ℝ := fun a => ξ (a + 1) - ξ a with hc
  have hec : elementCorrupt ξ ψ = ψ + c := by
    funext a; simp only [elementCorrupt, Pi.add_apply, hc]; ring
  obtain ⟨-, h2, h3⟩ := S70SOS.core x hx ψ c
  have hsum : c 0 + c 1 + c 2 = 0 := h2 ⟨ξ, fun a => rfl⟩
  obtain ⟨t, ht⟩ := h3 hsum
  have hv : npcVertices x (ψ + c) = (fun s => s + t) '' npcVertices x ψ := by
    rw [Set.image_add_right]
    ext s
    simp only [npcVertices, Set.mem_setOf_eq, Set.mem_preimage]
    simp only [ht _, Set.image_add_right, Set.mem_preimage]
  have hcp : closurePhase (ψ + c) = closurePhase ψ := by
    simp only [closurePhase, Fin.sum_univ_three, Pi.add_apply]; linarith
  rw [hec]
  refine ⟨⟨t, ht, hv⟩, hcp, ?_⟩
  unfold imageArea
  rw [hv]
  have himg : convexHull ℝ ((fun s => s + t) '' npcVertices x ψ) =
      (fun s => s + t) '' convexHull ℝ (npcVertices x ψ) := by
    have := (AffineEquiv.constVAdd ℝ Plane t).toAffineMap.image_convexHull (npcVertices x ψ)
    have hf : ⇑(AffineEquiv.constVAdd ℝ Plane t).toAffineMap = fun s => s + t := by
      funext s; simp [add_comm]
    rw [hf] at this
    exact this.symm
  rw [himg, Set.image_add_right, measure_preimage_add_right]
