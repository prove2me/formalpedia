-- Prove2me | solution 1 for Arxiv2012_05254.triad_image_true_up_to_shift
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:38:00.248804+00:00
-- url     : https://prove2.me/submissions/1b91dc03-d994-4d90-90cc-8130074ac1c6

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

open Arxiv2012_05254 in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (V : Fin 3 → Fin 3 → ℂ) (G : Fin 3 → ℂ) (hG : ∀ a, ‖G a‖ = 1) :
    ∃ t : Plane, ∀ s : Plane, triadImage x (corruptVis G V) id s = triadImage x V id (s + t) := by
  classical
  have hspan : affineSpan ℝ (Set.range x) = ⊤ := by
    rw [hx.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [finrank_euclideanSpace_fin]
  let b : AffineBasis (Fin 3) ℝ Plane := ⟨x, hx, hspan⟩
  have hb : ∀ a, b a = x a := fun a => rfl
  let θ : Fin 3 → ℝ := fun a => Complex.arg (G a)
  let φ : Plane →ᵃ[ℝ] ℝ := (θ 0 / (2 * Real.pi)) • b.coord 0 + (θ 1 / (2 * Real.pi)) • b.coord 1 +
    (θ 2 / (2 * Real.pi)) • b.coord 2
  have hφ : ∀ c, φ (x c) = θ c / (2 * Real.pi) := by
    intro c
    simp only [φ, AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hb,
      AffineBasis.coord_apply]
    fin_cases c <;> simp
  let t : Plane := (InnerProductSpace.toDual ℝ Plane).symm (LinearMap.toContinuousLinearMap φ.linear)
  have ht : ∀ u : Plane, ⟪u, t⟫ = φ.linear u := by
    intro u
    rw [real_inner_comm]
    simp [t, InnerProductSpace.toDual_symm_apply]
  have hGe : ∀ a, G a = Complex.exp (θ a * Complex.I) := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (G a)
    rw [hG a] at this; simp only [Complex.ofReal_one, one_mul] at this
    exact this.symm
  refine ⟨t, fun s => ?_⟩
  unfold triadImage
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  simp only [id, fringe, corruptVis]
  rw [inner_add_right, ht, show x (a + 1) - x a = x (a + 1) -ᵥ x a from rfl, AffineMap.linearMap_vsub,
    hφ, hφ, hGe a, hGe (a + 1), ← Complex.exp_conj]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show (starRingEnd ℂ) (↑(θ a) * Complex.I) = -(θ a * Complex.I) by
    simp [Complex.conj_ofReal]]
  have hE : (2 * (Real.pi : ℂ) * Complex.I * ((⟪x (a + 1) -ᵥ x a, s⟫ +
      (θ (a + 1) / (2 * Real.pi) -ᵥ θ a / (2 * Real.pi)) : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (⟪x (a + 1) -ᵥ x a, s⟫ : ℂ) +
        ((θ (a + 1) : ℂ) * Complex.I + -((θ a : ℂ) * Complex.I)) := by
    simp only [vsub_eq_sub]; push_cast; field_simp; ring
  rw [hE, Complex.exp_add, Complex.exp_add]
  ring
