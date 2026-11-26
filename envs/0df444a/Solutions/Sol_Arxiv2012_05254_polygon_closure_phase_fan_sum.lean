-- Prove2me | solution 1 for Arxiv2012_05254.polygon_closure_phase_fan_sum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:41:16.52203+00:00
-- url     : https://prove2.me/submissions/7476a9ee-cb50-43c2-9027-7b4cb5a424fe

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S78FS
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

lemma sum_spacing {n : ℕ} [NeZero n] (x : Fin n → Plane) : ∑ a, spacing x a = 0 := by
  unfold spacing
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun a => rfl)

lemma part1 {M : ℕ} (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b) :
    closurePhase (loopPhase ψ id) = ∑ q : Fin M, closurePhase (loopPhase ψ (fanTriad q)) := by
  have hR : ∀ q : Fin M, closurePhase (loopPhase ψ (fanTriad q)) =
      ψ q.succ.castSucc q.succ.succ + (ψ 0 q.castSucc.succ - ψ 0 q.succ.succ) := by
    intro q
    simp only [closurePhase, loopPhase, fanTriad, Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have e1 : (1 : Fin 3) + 1 = 2 := rfl
    have e2 : (2 : Fin 3) + 1 = 0 := rfl
    have e0 : (0 : Fin 3) + 1 = 1 := rfl
    rw [e0, e1, e2]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
    rw [hψ q.succ.succ 0, Fin.succ_castSucc]; ring
  simp only [hR, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : ∑ q : Fin M, ψ 0 q.castSucc.succ = ∑ i : Fin (M + 1), ψ 0 i.succ - ψ 0 (Fin.last (M + 1)) := by
    rw [Fin.sum_univ_castSucc (f := fun i : Fin (M + 1) => ψ 0 i.succ), Fin.succ_last]; ring
  have hB : ∑ q : Fin M, ψ 0 q.succ.succ = ∑ i : Fin (M + 1), ψ 0 i.succ - ψ 0 1 := by
    rw [Fin.sum_univ_succ (f := fun i : Fin (M + 1) => ψ 0 i.succ), Fin.succ_zero_eq_one]; ring
  rw [hA, hB]
  simp only [closurePhase, loopPhase, id]
  rw [Fin.sum_univ_castSucc, Fin.last_add_one]
  simp only [Fin.coeSucc_eq_succ]
  rw [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one, hψ (Fin.last (M + 1)) 0]
  ring

end S78FS

open Arxiv2012_05254 in
open scoped RealInnerProductSpace in
theorem solution {M : ℕ} (hM : 1 ≤ M) (x : Fin (M + 2) → Plane)
    (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b) :
    closurePhase (loopPhase ψ id) = ∑ q : Fin M, closurePhase (loopPhase ψ (fanTriad q)) ∧
    (AffineIndependent ℝ ![x (Fin.last (M + 1)), x 0, x 1] →
      (∃ s₀ : Plane, s₀ ∈ npc (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) ∩
          npc (spacing x 0) (ψ 0 1)) ∧
      ∀ s₀ ∈ npc (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) ∩ npc (spacing x 0) (ψ 0 1),
        recentredPhase (spacing x (Fin.last (M + 1))) (ψ (Fin.last (M + 1)) 0) s₀ = 0 ∧
        recentredPhase (spacing x 0) (ψ 0 1) s₀ = 0 ∧
        ∑ a, recentredPhase (spacing x a) (loopPhase ψ id a) s₀ = closurePhase (loopPhase ψ id)) := by
  refine ⟨S78FS.part1 ψ hψ, fun hx => ⟨?_, ?_⟩⟩
  · have hπ := Real.pi_ne_zero
    obtain ⟨t, ht⟩ := S78FS.exists_t _ hx
      ![0, -(ψ (Fin.last (M + 1)) 0) / (2 * Real.pi),
        -(ψ (Fin.last (M + 1)) 0) / (2 * Real.pi) - ψ 0 1 / (2 * Real.pi)]
    refine ⟨t, ?_, ?_⟩
    · have h := ht 0 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
      show 2 * Real.pi * ⟪spacing x (Fin.last (M + 1)), t⟫ + ψ (Fin.last (M + 1)) 0 = 0
      rw [spacing, Fin.last_add_one, h]; field_simp; ring
    · have h := ht 1 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h
      show 2 * Real.pi * ⟪spacing x 0, t⟫ + ψ 0 1 = 0
      rw [spacing, zero_add, h]; field_simp; ring
  · rintro s₀ ⟨h1, h2⟩
    have h1' : 2 * Real.pi * ⟪spacing x (Fin.last (M + 1)), s₀⟫ + ψ (Fin.last (M + 1)) 0 = 0 := h1
    have h2' : 2 * Real.pi * ⟪spacing x 0, s₀⟫ + ψ 0 1 = 0 := h2
    refine ⟨by simp only [recentredPhase]; linarith, by simp only [recentredPhase]; linarith, ?_⟩
    simp only [recentredPhase, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner,
      S78FS.sum_spacing, inner_zero_left, mul_zero, add_zero]
    rfl
