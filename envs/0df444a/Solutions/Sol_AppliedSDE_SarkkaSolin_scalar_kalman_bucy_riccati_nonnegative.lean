-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.scalar_kalman_bucy_riccati_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:28:36.888267+00:00
-- url     : https://prove2.me/submissions/0edb29a3-e99e-4ec2-b0c1-d748cf5b2345

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped Topology

theorem solution
    (F H Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R)
    (P : ℝ → ℝ) (hP0 : 0 ≤ P 0)
    (hcont : Continuous P)
    (hdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ P t)
    (hode : ∀ t : ℝ, 0 ≤ t →
      deriv P t = 2 * F * P t + Q - (H ^ 2 / R) * (P t) ^ 2) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ P t := by
  intro t ht
  let A : ℝ → ℝ := fun s => 2 * F - (H ^ 2 / R) * P s
  let I : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, A s
  let M : ℝ → ℝ := fun u => Real.exp (-I u)
  let G : ℝ → ℝ := fun u => M u * P u
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hI (s : ℝ) : HasDerivAt I (A s) s := by
    change HasDerivAt (fun u => ∫ z in (0 : ℝ)..u, A z) (A s) s
    exact intervalIntegral.integral_hasDerivAt_right
      (hAcont.intervalIntegrable (0 : ℝ) s)
      (hAcont.aestronglyMeasurable.stronglyMeasurableAtFilter)
      hAcont.continuousAt
  have hM (s : ℝ) : HasDerivAt M (-(A s) * M s) s := by
    have hd := (Real.hasDerivAt_exp (-I s)).comp s ((hI s).neg)
    have hcoeff :
        Real.exp (-I s) * (-(A s)) = -(A s) * M s := by
      dsimp [M]
      ring
    exact hcoeff ▸ hd
  have hP (s : ℝ) (hs0 : 0 ≤ s) :
      HasDerivAt P (A s * P s + Q) s := by
    have hderiv : deriv P s = A s * P s + Q := by
      rw [hode s hs0]
      dsimp [A]
      ring
    simpa only [hderiv] using ((hdiff s hs0).hasDerivAt)
  have hG : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt G (M s * Q) s := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    have hp := (hM s).mul (hP s hs.1)
    have hc :
        (-(A s) * M s) * P s + M s * (A s * P s + Q) =
        M s * Q := by ring
    exact hc ▸ hp
  have hMQcont : Continuous (fun s : ℝ => M s * Q) := by
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    (hMQcont.intervalIntegrable (0 : ℝ) t)
  have hG0 : G 0 = P 0 := by
    simp [G, M, I]
  have hGt : G t = M t * P t := rfl
  rw [hG0, hGt] at hFTC
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, M s * Q := by
    apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le hQ
  have hbound : 0 ≤ M t * P t := by
    linarith
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-I t))).mp hbound
