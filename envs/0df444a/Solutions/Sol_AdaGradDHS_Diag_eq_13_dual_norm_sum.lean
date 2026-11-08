-- Prove2me | solution 1 for AdaGradDHS.Diag.eq_13_dual_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:55:37.458673+00:00
-- url     : https://prove2.me/submissions/493c0a03-afea-4ae8-85ad-4d7e2f5e267d

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm

namespace AdaGradDHS.Diag.Aux_ADG

theorem key (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) {δ : ℝ} (hδ : 0 ≤ δ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t / (δ + Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ)) ≤
      2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hS : ∑ τ ∈ Finset.Icc 1 (T + 1), a τ = (∑ τ ∈ Finset.Icc 1 T, a τ) + a (T + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1), hS]
    set S := ∑ τ ∈ Finset.Icc 1 T, a τ with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => ha t
    have hat := ha (T + 1)
    set x := a (T + 1) with hx
    set u := Real.sqrt (S + x) with hu
    set v := Real.sqrt S with hv
    have hu2 : u ^ 2 = S + x := Real.sq_sqrt (by linarith)
    have hv2 : v ^ 2 = S := Real.sq_sqrt hS0
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
    have step : x / (δ + u) ≤ 2 * u - 2 * v := by
      rcases hu0.lt_or_eq with hpos | hzero
      · have h1 : x / (δ + u) ≤ x / u :=
          div_le_div_of_nonneg_left hat hpos (by linarith)
        have h2 : x / u ≤ 2 * u - 2 * v := by
          rw [div_le_iff₀ hpos]
          nlinarith [sq_nonneg (u - v)]
        linarith
      · have hx0 : x = 0 := by
          have : S + x = 0 := by rw [← hu2, ← hzero]; ring
          linarith
        rw [hx0, zero_div]
        linarith
    linarith

end AdaGradDHS.Diag.Aux_ADG

open AdaGradDHS.Diag AdaGradDHS.Diag.Aux_ADG in
theorem solution {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ∑ i, (g t i) ^ 2 / (δ + accNorm g t i) ≤ 2 * ∑ i, accNorm g T i := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [accNorm]
  exact key (fun t => (g t i) ^ 2) (fun t => sq_nonneg _) hδ T
