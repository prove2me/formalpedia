-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:10:16.715855+00:00
-- url     : https://prove2.me/submissions/a3043537-2817-41e5-b54c-fe34f29ef022

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting
import Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_4_6

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

/-- The Riccati equation (4.3) for `m̃ = −ψ′/ψ`. -/
lemma ads_riccati (M : Model) (hM : M.Valid) (r : ℝ) (ψ : ℝ → ℝ)
    (hψ : IsDecreasingSolution M r ψ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (mtilde ψ)
      (mtilde ψ x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * mtilde ψ x - 2 * r / M.σ x ^ 2) x := by
  have hs := hM.σ_sq_pos x hx
  have hpos := hψ.pos x hx
  have hnhds : Ioi (0:ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hx
  have h1 : HasDerivAt ψ (deriv ψ x) x :=
    (((hψ.smooth.differentiableOn (by norm_num)) x hx).differentiableAt hnhds).hasDerivAt
  have h2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    ((((hψ.smooth.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
      (by norm_num)) x hx).differentiableAt hnhds).hasDerivAt
  have h3 := h2.neg.div h1 hpos.ne'
  have hode := hψ.ode x hx
  have h4 : HasDerivAt (mtilde ψ)
      ((-deriv (deriv ψ) x * ψ x - -deriv ψ x * deriv ψ x) / ψ x ^ 2) x := h3
  convert h4 using 1
  have hσ : M.σ x ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hpp : deriv (deriv ψ) x = 2 * (r * ψ x - M.μ x * deriv ψ x) / M.σ x ^ 2 := by
    rw [eq_div_iff hs.ne']
    linarith
  rw [hpp]
  unfold mtilde
  field_simp
  ring

theorem solution (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (r : ℝ) (hr : 0 ≤ r) (ψ : ℝ → ℝ) (hψ : IsDecreasingSolution M r ψ) :
    AntitoneOn (mtilde ψ) (Ioi 0) := by
  have hlt := lemma_4_6 M hM hCi hCii1 r hr ψ hψ
  have hmd : ∀ x, 0 < x → HasDerivAt (mtilde ψ)
      (mtilde ψ x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * mtilde ψ x - 2 * r / M.σ x ^ 2) x :=
    fun x hx => ads_riccati M hM r ψ hψ x hx
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hmd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hmd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    rw [(hmd x hx0).deriv]
    have hs := hM.σ_sq_pos x hx0
    have hσ : M.σ x ≠ 0 := by
      intro h; rw [h] at hs; simp at hs
    have hpos := hψ.pos x hx0
    -- ψ′ ≤ 0, hence m̃ ≥ 0
    have hψ'le : deriv ψ x ≤ 0 := by
      have := hψ.anti.derivWithin_nonpos (x := x)
      rwa [derivWithin_of_isOpen isOpen_Ioi hx0] at this
    have hm0 : 0 ≤ mtilde ψ x := by
      unfold mtilde
      exact div_nonneg (by linarith) hpos.le
    set S := Real.sqrt (M.μ x ^ 2 + 2 * r * M.σ x ^ 2) with hS
    have hSsq : S ^ 2 = M.μ x ^ 2 + 2 * r * M.σ x ^ 2 := Real.sq_sqrt (by positivity)
    have hμS : M.μ x ≤ S := by
      have := Real.abs_le_sqrt (show M.μ x ^ 2 ≤ M.μ x ^ 2 + 2 * r * M.σ x ^ 2 by nlinarith)
      exact le_trans (le_abs_self _) this
    have hp : M.phi1 r x = (M.μ x + S) / M.σ x ^ 2 := rfl
    have hfac : mtilde ψ x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * mtilde ψ x - 2 * r / M.σ x ^ 2 =
        (mtilde ψ x - (M.μ x + S) / M.σ x ^ 2) * (mtilde ψ x + (S - M.μ x) / M.σ x ^ 2) := by
      rw [show (mtilde ψ x - (M.μ x + S) / M.σ x ^ 2) * (mtilde ψ x + (S - M.μ x) / M.σ x ^ 2) =
          mtilde ψ x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * mtilde ψ x +
            (M.μ x ^ 2 - S ^ 2) / (M.σ x ^ 2) ^ 2 by field_simp; ring]
      rw [hSsq]
      field_simp
      ring
    rw [hfac]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have := hlt x hx0
      rw [hp] at this
      linarith
    · have : 0 ≤ (S - M.μ x) / M.σ x ^ 2 := div_nonneg (by linarith) hs.le
      linarith
