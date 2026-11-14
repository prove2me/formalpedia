-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreIntegration
-- name    : row23_rh_supp_RHLegendreIntegration
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:59:38.646803+00:00
-- url     : https://prove2.me/theorems/92751b2f-7960-4f8a-a8fe-9a01bf33089e
-- title:
--   Row 23 RH support: RHLegendreIntegration
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRodrigues
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
 theorem polynomial_integration_by_parts (m : ℕ) (p : ℝ[X]) (F : ℕ → ℝ → ℂ)
    (hc : ∀ k ≤ m, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1))
    (hd : ∀ k < m, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t)
    (hb : ∀ k < m, (derivative^[k] p).eval 0=0 ∧ (derivative^[k] p).eval 1=0) :
    (∫ t : ℝ in 0..1, ((p.eval t:ℝ):ℂ)*F m t) =
      (-1:ℂ)^m * (∫ t : ℝ in 0..1, (((derivative^[m] p).eval t:ℝ):ℂ)*F 0 t) := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    have hu : IntervalIntegrable (fun t : ℝ => ((p.derivative.eval t:ℝ):ℂ)) volume 0 1 :=
      (Complex.continuous_ofReal.comp p.derivative.continuous).intervalIntegrable 0 1
    have hv : IntervalIntegrable (F (m+1)) volume 0 1 := (hc (m+1) (by omega)).intervalIntegrable
    have step := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t (_ : t ∈ Set.uIcc (0:ℝ) 1) => (p.hasDerivAt t).ofReal_comp)
      (hd m (by omega)) hu hv
    have hp0 : p.eval 0=0 := by simpa using (hb 0 (by omega)).1
    have hp1 : p.eval 1=0 := by simpa using (hb 0 (by omega)).2
    rw [hp0,hp1,Complex.ofReal_zero,zero_mul,zero_mul,sub_self,zero_sub] at step
    have hc' : ∀ k ≤ m, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1) := fun k hk => hc k (by omega)
    have hd' : ∀ k < m, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t :=
      fun k hk => hd k (by omega)
    have hb' : ∀ k < m, (derivative^[k] p.derivative).eval 0=0 ∧
        (derivative^[k] p.derivative).eval 1=0 := by
      intro k hk
      simpa only [Function.iterate_succ_apply] using hb (k+1) (by omega)
    rw [step,ih p.derivative hc' hd' hb']
    simp only [Function.iterate_succ_apply,pow_succ]
    ring
 theorem weighted_integration_by_parts (m : ℕ) (F : ℕ → ℝ → ℂ)
    (hc : ∀ k ≤ m, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1))
    (hd : ∀ k < m, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t) :
    (∫ t : ℝ in 0..1, (weight m t:ℂ)*F m t) =
      (-1:ℂ)^m * (∫ t : ℝ in 0..1, ((iteratedDeriv m (weight m) t:ℝ):ℂ)*F 0 t) := by
  have hb : ∀ k < m, (derivative^[k] (densityPolynomial m)).eval 0=0 ∧
      (derivative^[k] (densityPolynomial m)).eval 1=0 := by
    intro k hk
    constructor
    · rw [←iteratedDeriv_weight,derivative_at_zero m k hk]
    · rw [←iteratedDeriv_weight,derivative_at_one m k hk]
  simpa only [densityPolynomial_eval,←iteratedDeriv_weight] using
    polynomial_integration_by_parts m (densityPolynomial m) F hc hd hb
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.polynomial_integration_by_parts
#print axioms DusartLegendreSmoothing.weighted_integration_by_parts


