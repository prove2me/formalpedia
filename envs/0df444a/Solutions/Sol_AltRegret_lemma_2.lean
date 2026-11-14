-- Prove2me | solution 1 for AltRegret.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T19:27:07.276077+00:00
-- url     : https://prove2.me/submissions/5b7133ea-8028-4b42-9c00-7faacb5a547c

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OneStep
open Set

private lemma scalar_bound (η β a z : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/8) (hβ : β = η/4)
    (ha : a ∈ Icc (-2 : ℝ) 2) (hz : z ∈ Icc (-2 : ℝ) 2) :
    Real.exp (-η * (a+z) + β*(a^2-z^2)) ≤ 1 - η*(1-a/2)*(a+z) := by
  let f := fun y : ℝ => Real.exp (-η*y - β*y^2)
  let k := fun y : ℝ => -η - 2*β*y
  have hf (y : ℝ) : HasDerivAt f (f y * k y) y := by
    dsimp [f,k]
    convert (((hasDerivAt_id y).const_mul (-η)).sub
      (((hasDerivAt_id y).pow 2).const_mul β)).exp using 1 <;> simp <;> ring
  have hk (y : ℝ) : HasDerivAt k (-2*β) y := by
    dsimp [k]
    convert (hasDerivAt_const y (-η)).sub ((hasDerivAt_id y).const_mul (2*β)) using 1 <;> first | rfl | ring
  have hf' (y : ℝ) : HasDerivAt (fun w => f w * k w) (f y * (k y ^ 2 - 2*β)) y := by
    exact ((hf y).mul (hk y)).congr_deriv (by ring)
  have hconc : ConcaveOn ℝ (Icc (-2 : ℝ) 2) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).hasDerivWithinAt) (fun y _ => (hf' y).hasDerivWithinAt)
    intro y hy
    obtain ⟨hy₁,hy₂⟩ := interior_subset hy
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hb : 0 ≤ β := by linarith
    have h₁ : -2*η ≤ k y := by dsimp [k]; nlinarith [mul_nonneg hb (sub_nonneg.mpr hy₂)]
    have h₂ : k y ≤ 0 := by dsimp [k]; nlinarith [mul_nonneg hb (sub_nonneg.mpr hy₁)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (neg_nonneg.mpr h₂),
      mul_nonneg hη (sub_nonneg.mpr hη'), mul_nonneg hη (sub_nonneg.mpr h₁)]
  have hma : -a ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hline : f z ≤ f (-a) + (f (-a)*k (-a))*(z-(-a)) := by
    rcases lt_trichotomy (-a) z with h|h|h
    · have hsl := hconc.slope_le_of_hasDerivAt hma hz h (hf (-a))
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hsl
      linarith
    · rw [← h]; ring_nf; rfl
    · have hsl := hconc.le_slope_of_hasDerivAt hz hma h (hf (-a))
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hsl
      linarith
  have hid : Real.exp (-η*(a+z)+β*(a^2-z^2)) * f (-a) = f z := by
    dsimp [f]; rw [← Real.exp_add]; congr 1; ring
  apply le_of_mul_le_mul_right (a := f (-a)) _ (Real.exp_pos _)
  rw [hid]
  calc
    _ ≤ _ := hline
    _ = _ := by dsimp [k]; rw [hβ]; ring

private lemma weighted_bound {d : ℕ} (η β : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/8) (hβ : β = η/4)
    (p a z : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ha : ∀ i, a i ∈ Icc (-2 : ℝ) 2) (hz : ∀ i, z i ∈ Icc (-2 : ℝ) 2) :
    let M := ∑ i, p i * (1-a i/2) * (a i+z i)
    ∑ i, p i * Real.exp (η*(M-a i-z i)+β*((a i)^2-(z i)^2)) ≤ 1 := by
  intro M
  let g := fun i => -η*(a i+z i)+β*((a i)^2-(z i)^2)
  have hsum : (∑ i, p i * Real.exp (g i)) ≤ 1-η*M := by
    calc
      _ ≤ ∑ i, p i*(1-η*(1-a i/2)*(a i+z i)) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (scalar_bound η β _ _ hη hη' hβ (ha i) (hz i)) (hp i)
      _ = _ := by
        dsimp [M]
        rw [Finset.mul_sum]
        simp_rw [show ∀ i, p i*(1-η*(1-a i/2)*(a i+z i)) =
          p i - η*(p i*(1-a i/2)*(a i+z i)) by intro i; ring]
        rw [Finset.sum_sub_distrib,hs]
  calc
    _ = (∑ i, p i*Real.exp (g i))*Real.exp (η*M) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [g]; ring
    _ ≤ Real.exp (-(η*M))*Real.exp (η*M) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact hsum.trans (by linarith [Real.add_one_le_exp (-(η*M))])
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end OneStep

theorem solution (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hβ : β = η / 4) {d : ℕ}
    (p ξ x z : Fin d → ℝ) (hp : p ∈ stdSimplex ℝ (Fin d))
    (hξ : ∀ i, ξ i ∈ Set.Icc (-2 : ℝ) 2) (hpξ : ∑ i, p i * ξ i = 0)
    (hx : ∀ i, x i = p i * (1 - ξ i / 2)) (hz : ∀ i, z i ∈ Set.Icc (-2 : ℝ) 2) :
    Real.log (∑ i, p i * Real.exp
      (η * (∑ j, (ξ j + z j) * x j - ξ i - z i) + β * (ξ i ^ 2 - z i ^ 2))) ≤ 0 := by
  apply Real.log_nonpos (Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)
  have hM : (∑ j, (ξ j + z j) * x j) = ∑ j, p j * (1 - ξ j / 2) * (ξ j + z j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hx, mul_comm]
  rw [hM]
  exact OneStep.weighted_bound η β hη0 hη hβ p ξ z hp.1 hp.2 hξ hz
