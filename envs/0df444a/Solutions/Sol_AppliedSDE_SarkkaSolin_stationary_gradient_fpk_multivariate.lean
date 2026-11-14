-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_gradient_fpk_multivariate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:41:16.28132+00:00
-- url     : https://prove2.me/submissions/58b7cd98-ba96-4326-aed5-7452eb638b52

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Topology

theorem solution
    (n : ℕ) (q : ℝ) (hq : 0 < q)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (hInt : Integrable (fun x : Fin n → ℝ => Real.exp (-(v x / q))))
    (hZ : 0 < ∫ x : Fin n → ℝ, Real.exp (-(v x / q))) :
    let Z : ℝ := ∫ x : Fin n → ℝ, Real.exp (-(v x / q))
    let p : (Fin n → ℝ) → ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
    (∀ x : Fin n → ℝ, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ x : Fin n → ℝ,
      (∑ i : Fin n, fderiv ℝ (fun y : Fin n → ℝ =>
          (-(1 / 2 : ℝ) * fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) x
          (Pi.single i (1 : ℝ))) =
      q / 2 * ∑ i : Fin n, fderiv ℝ
        (fun y : Fin n → ℝ => fderiv ℝ p y (Pi.single i (1 : ℝ))) x
        (Pi.single i (1 : ℝ))) := by
  let Z : ℝ := ∫ x : Fin n → ℝ, Real.exp (-(v x / q))
  let u : (Fin n → ℝ) → ℝ := fun y => -(v y / q)
  let p : (Fin n → ℝ) → ℝ := fun y => Z⁻¹ * Real.exp (u y)
  change (∀ x : Fin n → ℝ, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ x : Fin n → ℝ,
      (∑ i : Fin n, fderiv ℝ (fun y : Fin n → ℝ =>
          (-(1 / 2 : ℝ) * fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) x
          (Pi.single i (1 : ℝ))) =
      q / 2 * ∑ i : Fin n, fderiv ℝ
        (fun y : Fin n → ℝ => fderiv ℝ p y (Pi.single i (1 : ℝ))) x
        (Pi.single i (1 : ℝ)))
  have hqne : q ≠ 0 := ne_of_gt hq
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hucont : ContDiff ℝ 2 u := by
    dsimp [u]
    exact (hv.div_const q).neg
  have hpcont : ContDiff ℝ 2 p := by
    dsimp [p]
    exact contDiff_const.mul hucont.exp
  have hudu (y : Fin n → ℝ) :
      fderiv ℝ u y = (-q⁻¹) • fderiv ℝ v y := by
    have heq : u = fun z : Fin n → ℝ => (-q⁻¹) * v z := by
      funext z
      dsimp [u]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact fderiv_const_mul ((hv.differentiable (by norm_num)) y) (-q⁻¹)
  have hpderiv (y : Fin n → ℝ) : fderiv ℝ p y =
      (Z⁻¹) • (Real.exp (u y) • ((-q⁻¹) • fderiv ℝ v y)) := by
    have hud : DifferentiableAt ℝ u y :=
      (hucont.differentiable (by norm_num)) y
    have hd := fderiv_const_mul hud.exp (Z⁻¹)
    change fderiv ℝ p y =
      (Z⁻¹) • (Real.exp (u y) • ((-q⁻¹) • fderiv ℝ v y))
    rw [hd, fderiv_exp hud, hudu y]
  have hflux (y : Fin n → ℝ) (i : Fin n) :
      (-(1 / 2 : ℝ) * fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y =
        q / 2 * fderiv ℝ p y (Pi.single i (1 : ℝ)) := by
    rw [hpderiv y]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp [p]
    field_simp [hqne]
  have hdir (x : Fin n → ℝ) (i : Fin n) : DifferentiableAt ℝ
      (fun y : Fin n → ℝ => fderiv ℝ p y (Pi.single i (1 : ℝ))) x := by
    have hd : ContDiff ℝ 1 (fderiv ℝ p) :=
      hpcont.fderiv_right (by norm_num)
    have hd' : ContDiff ℝ 1
        (fun y : Fin n → ℝ => fderiv ℝ p y (Pi.single i (1 : ℝ))) :=
      hd.clm_apply contDiff_const
    exact (hd'.differentiable (by norm_num)) x
  refine ⟨?_, ?_, ?_⟩
  · intro x
    dsimp [p]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le
  · dsimp [p, Z]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hZne
  · intro x
    calc
      (∑ i : Fin n, fderiv ℝ (fun y : Fin n → ℝ =>
          (-(1 / 2 : ℝ) * fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) x
          (Pi.single i (1 : ℝ))) =
        ∑ i : Fin n, fderiv ℝ (fun y : Fin n → ℝ =>
          q / 2 * fderiv ℝ p y (Pi.single i (1 : ℝ))) x
          (Pi.single i (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [show (fun y : Fin n → ℝ =>
            (-(1 / 2 : ℝ) * fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) =
            (fun y : Fin n → ℝ => q / 2 * fderiv ℝ p y
              (Pi.single i (1 : ℝ))) from funext (fun y => hflux y i)]
      _ = q / 2 * ∑ i : Fin n,
          fderiv ℝ (fun y : Fin n → ℝ =>
            fderiv ℝ p y (Pi.single i (1 : ℝ))) x
            (Pi.single i (1 : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [fderiv_const_mul (hdir x i) (q / 2)]
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
