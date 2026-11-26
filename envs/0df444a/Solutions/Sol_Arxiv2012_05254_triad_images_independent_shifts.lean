-- Prove2me | solution 1 for Arxiv2012_05254.triad_images_independent_shifts
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:46:51.59847+00:00
-- url     : https://prove2.me/submissions/9dad4486-2e93-4776-a030-5ecde586822e

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S81T
open Arxiv2012_05254
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

lemma ai3 (p0 p1 p2 : Plane) (h : cross (p1 - p0) (p2 - p0) ≠ 0) :
    AffineIndependent ℝ ![p0, p1, p2] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw (0 : Plane),
    Finset.weightedVSubOfPoint_apply] at hv
  simp only [Fin.sum_univ_three, vsub_eq_sub, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hv
  rw [Fin.sum_univ_three] at hw
  have h0 := congrArg (fun v : Plane => v 0) hv
  have h1 := congrArg (fun v : Plane => v 1) hv
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1
  unfold cross at h
  simp only [PiLp.sub_apply] at h
  have hw0 : w 0 = -w 1 - w 2 := by linarith
  rw [hw0] at h0 h1
  have e1 : w 1 * ((p1 0 - p0 0) * (p2 1 - p0 1) - (p1 1 - p0 1) * (p2 0 - p0 0)) = 0 := by
    linear_combination (p2 1 - p0 1) * h0 - (p2 0 - p0 0) * h1
  have e2 : w 2 * ((p1 0 - p0 0) * (p2 1 - p0 1) - (p1 1 - p0 1) * (p2 0 - p0 0)) = 0 := by
    linear_combination -(p1 1 - p0 1) * h0 + (p1 0 - p0 0) * h1
  have hw1 := (mul_eq_zero.1 e1).resolve_right h
  have hw2 := (mul_eq_zero.1 e2).resolve_right h
  intro i; fin_cases i
  · simp [hw0, hw1, hw2]
  · exact hw1
  · exact hw2

lemma unit_exp (z : ℂ) (h : ‖z‖ = 1) : z = Complex.exp (Complex.arg z * Complex.I) := by
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [h] at this; simpa using this.symm

def P (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]

noncomputable def y4 : Fin 4 → Plane := ![P 0 0, P 1 0, P 0 1, P (1/2) 0]
def W4 : Fin 4 → Fin 4 → ℂ := fun a b => if (a = 0 ∧ b = 1) ∨ (a = 3 ∧ b = 0) then 1 else 0
def H4 : Fin 4 → ℂ := ![1, 1, 1, Complex.I]

lemma img1 (V : Fin 4 → Fin 4 → ℂ) (s : Plane) : triadImage y4 V ![0, 1, 2] s =
    2 * (fringe (y4 1 - y4 0) (V 0 1) s).re + 2 * (fringe (y4 2 - y4 1) (V 1 2) s).re +
      2 * (fringe (y4 0 - y4 2) (V 2 0) s).re := by
  simp [triadImage, Fin.sum_univ_three]

lemma img2 (V : Fin 4 → Fin 4 → ℂ) (s : Plane) : triadImage y4 V ![0, 2, 3] s =
    2 * (fringe (y4 2 - y4 0) (V 0 2) s).re + 2 * (fringe (y4 3 - y4 2) (V 2 3) s).re +
      2 * (fringe (y4 0 - y4 3) (V 3 0) s).re := by
  simp [triadImage, Fin.sum_univ_three]

end S81T

open Arxiv2012_05254 S81T in
theorem solution {N : ℕ} (x : Fin N → Plane) (V : Fin N → Fin N → ℂ)
    (G : Fin N → ℂ) (hG : ∀ a, ‖G a‖ = 1) :
    (∀ v : Fin 3 → Fin N, AffineIndependent ℝ (x ∘ v) →
      ∃ t : Plane, ∀ s : Plane, triadImage x (corruptVis G V) v s = triadImage x V v (s + t)) ∧
    ∃ (y : Fin 4 → Plane) (W : Fin 4 → Fin 4 → ℂ) (H : Fin 4 → ℂ), (∀ a, ‖H a‖ = 1) ∧
      AffineIndependent ℝ (y ∘ (![0, 1, 2] : Fin 3 → Fin 4)) ∧
      AffineIndependent ℝ (y ∘ (![0, 2, 3] : Fin 3 → Fin 4)) ∧
      ¬ ∃ t : Plane, ∀ s : Plane,
        triadImage y (corruptVis H W) ![0, 1, 2] s = triadImage y W ![0, 1, 2] (s + t) ∧
        triadImage y (corruptVis H W) ![0, 2, 3] s = triadImage y W ![0, 2, 3] (s + t) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht⟩ := exists_t (x ∘ v) hv (fun c => Complex.arg (G (v c)) / (2 * Real.pi))
    refine ⟨t, fun s => ?_⟩
    unfold triadImage
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 2
    have h := ht a (a + 1)
    simp only [Function.comp] at h
    unfold fringe corruptVis
    set u := x (v (a + 1)) - x (v a)
    set ξ0 := Complex.arg (G (v a))
    set ξ1 := Complex.arg (G (v (a + 1)))
    rw [unit_exp (G (v a)) (hG _), unit_exp (G (v (a + 1))) (hG _), inner_add_right, h,
      ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_comm _ (V _ _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  · refine ⟨y4, W4, H4, ?_, ?_, ?_, ?_⟩
    · intro a; fin_cases a <;> simp [H4]
    · have e : y4 ∘ (![0, 1, 2] : Fin 3 → Fin 4) = ![P 0 0, P 1 0, P 0 1] := by
        funext i; fin_cases i <;> rfl
      rw [e]; apply ai3; simp [cross, P]
    · have e : y4 ∘ (![0, 2, 3] : Fin 3 → Fin 4) = ![P 0 0, P 0 1, P (1/2) 0] := by
        funext i; fin_cases i <;> rfl
      rw [e]; apply ai3; simp [cross, P]
    · rintro ⟨t, ht⟩
      have h1 := (ht 0).1
      have h2 := (ht (-t)).2
      rw [img1, img1] at h1
      rw [img2, img2, neg_add_cancel] at h2
      simp [fringe, corruptVis, W4, H4, y4, P, inner_zero_right] at h1 h2
      set A := ⟪(WithLp.toLp 2 ![(1:ℝ), 0] : Plane) - WithLp.toLp 2 ![0, 0], t⟫ with hA
      set B := ⟪(WithLp.toLp 2 ![(0:ℝ), 0] : Plane) - WithLp.toLp 2 ![2⁻¹, 0], t⟫ with hB
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (A : ℂ) = ((2 * Real.pi * A : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_ofReal_mul_I_re] at h1
      rw [show -(2 * (Real.pi : ℂ) * Complex.I * (B : ℂ)) = ((-(2 * Real.pi * B) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_ofReal_mul_I_im] at h2
      have hAB : A = -2 * B := by
        simp only [hA, hB, inner_sub_left, PiLp.inner_apply, Fin.sum_univ_two]
        simp
        ring
      rw [show 2 * Real.pi * A = 2 * (-(2 * Real.pi * B)) by rw [hAB]; ring, Real.cos_two_mul] at h1
      have := Real.sin_sq_add_cos_sq (-(2 * Real.pi * B))
      rw [h2] at this
      nlinarith
