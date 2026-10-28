-- Prove2me | solution 1 for AccelMM.BTMap.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:33:37.230399+00:00
-- url     : https://prove2.me/submissions/321222af-f4b9-4300-82e4-14c5be5bafe2

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

open scoped InnerProductSpace

namespace Aux_AccelMM_T42

open AccelMM.BTMap

lemma descent {n : ℕ} (f : E n → ℝ) (hf : Differentiable ℝ f) (X : Set (E n))
    (hX : Convex ℝ X) (μ : ℝ) (hS : SmoothOn f X μ) (x z : E n) (hx : x ∈ X) (hz : z ∈ X) :
    f z ≤ f x + ⟪gradient f x, z - x⟫_ℝ + μ / 2 * ‖z - x‖ ^ 2 := by
  set v := z - x with hv
  set c := ⟪gradient f x, v⟫_ℝ with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - μ / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • v), v⟫_ℝ - c - μ * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hfd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) := (hf _).hasFDerivAt
    have h1 := hfd.comp_hasDerivAt t hline
    have hg : fderiv ℝ f (x + t • v) v = ⟪gradient f (x + t • v), v⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [hg] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => μ / 2 * s ^ 2 * ‖v‖ ^ 2) (μ * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (μ / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hmem : x + t • v ∈ X := hX.add_smul_sub_mem hx hz ⟨ht.1.le, ht.2.le⟩
      have hL := hS (x + t • v) hmem x hx
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hi : ⟪gradient f (x + t • v), v⟫_ℝ - c ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := by
        rw [hc, ← inner_sub_left]
        exact real_inner_le_norm _ _
      rw [hn] at hL
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hL (norm_nonneg v)]
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = z := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  linarith

end Aux_AccelMM_T42

open AccelMM.BTMap in
theorem solution {n : ℕ} (f : E n → ℝ) (hf : Differentiable ℝ f)
    (X : Set (E n)) (hX : Convex ℝ X) (xstar : E n) (hxstarX : xstar ∈ X)
    (hmin : ∀ x, f xstar ≤ f x) (d : E n) (μ γ δ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hF1 : SmoothOn f X μ) (hF2 : PLOn f (X0 f X d) γ xstar)
    (Pi : E n → E n) (hP1 : ∀ x, f (Pi x) ≤ f x)
    (g : E n → E n → ℝ) (hg : IsMajorant g f)
    (hgδ : ∀ x ∈ X, ∀ y ∈ X, g x y - f x ≤ δ / 2 * ‖x - y‖ ^ 2)
    (xt xm xt1 : E n) (hxt : xt ∈ X0 f X d) (hxt1 : xt1 ∈ X0 f X d)
    (hvirt : xt - (1 / (μ + δ)) • gradient f xt ∈ X)
    (hxm : ∀ z, g xm xt ≤ g z xt) (hstep : xt1 = Pi xm) :
    f xt1 - f xstar ≤ (1 - γ / (μ + δ)) * (f xt - f xstar) := by
  have hxtX : xt ∈ X := hxt.1
  set G := gradient f xt with hG
  set η := 1 / (μ + δ) with hη
  set z := xt - η • G with hz
  have hμδ : 0 < μ + δ := by linarith
  have hηpos : 0 < η := by positivity
  have hημ : η * (μ + δ) = 1 := by rw [hη]; field_simp
  -- chain of inequalities
  have c1 : f xt1 ≤ f xm := by rw [hstep]; exact hP1 xm
  have c2 : f xm ≤ g xm xt := (hg xm xt).1
  have c3 : g xm xt ≤ g z xt := hxm z
  have c4 : g z xt ≤ f z + δ / 2 * ‖z - xt‖ ^ 2 := by
    have := hgδ z hvirt xt hxtX; linarith
  have c5 := Aux_AccelMM_T42.descent f hf X hX μ hF1 xt z hxtX hvirt
  have hzx : z - xt = -(η • G) := by rw [hz]; abel
  have hin : ⟪gradient f xt, z - xt⟫_ℝ = -(η * ‖G‖ ^ 2) := by
    rw [hzx, inner_neg_right, real_inner_smul_right, ← hG, real_inner_self_eq_norm_sq]
  have hnz : ‖z - xt‖ ^ 2 = η ^ 2 * ‖G‖ ^ 2 := by
    rw [hzx, norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg hηpos.le]
  rw [hin, hnz] at c5
  rw [hnz] at c4
  have hdesc : f xt1 ≤ f xt - η * ‖G‖ ^ 2 / 2 := by
    have : f xt1 ≤ f xt - η * ‖G‖ ^ 2 + (μ + δ) / 2 * (η ^ 2 * ‖G‖ ^ 2) := by
      nlinarith
    have e : (μ + δ) / 2 * (η ^ 2 * ‖G‖ ^ 2) = η * ‖G‖ ^ 2 / 2 := by
      have : (μ + δ) * η ^ 2 = η := by nlinarith
      nlinarith
    linarith
  have hPL := hF2 xt hxt
  rw [← hG] at hPL
  have hPL' : 2 * γ * (f xt - f xstar) ≤ ‖G‖ ^ 2 := by
    have h2 : 1 / (2 * γ) * ‖G‖ ^ 2 = ‖G‖ ^ 2 / (2 * γ) := by ring
    rw [h2, le_div_iff₀ (by positivity)] at hPL
    linarith
  have hγη : γ / (μ + δ) = γ * η := by rw [hη]; ring
  rw [hγη]
  nlinarith [mul_le_mul_of_nonneg_left hPL' hηpos.le]
