-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePolynomialPairing
-- name    : row23_rh_supp_RHLegendrePolynomialPairing
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:05:07.086079+00:00
-- url     : https://prove2.me/theorems/261c1ee5-110d-4a78-bc71-8e3b9608a95f
-- title:
--   Row 23 RH support: RHLegendrePolynomialPairing
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreIntegration
import Definitions.Def_row23_rh_supp_RHLegendreAverage
set_option autoImplicit false
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
 theorem second_derivative_polynomial_pairing (m : ℕ) (hm : 2 ≤ m) (q : ℝ[X]) :
    (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*q.eval t) =
      ∫ t : ℝ in 0..1, weight m t*q.derivative.derivative.eval t := by
  let F := fun (k : ℕ) (t : ℝ) => (((derivative^[k] q).eval t:ℝ):ℂ)
  have hc : ∀ k ≤ 2, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1) := by
    intro k hk
    exact (Complex.continuous_ofReal.comp (derivative^[k] q).continuous).continuousOn
  have hd : ∀ k < 2, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t := by
    intro k hk t ht
    simpa only [F,Function.iterate_succ_apply'] using ((derivative^[k] q).hasDerivAt t).ofReal_comp
  have hb : ∀ k < 2, (derivative^[k] (densityPolynomial m)).eval 0=0 ∧
      (derivative^[k] (densityPolynomial m)).eval 1=0 := by
    intro k hk
    constructor
    · rw [←iteratedDeriv_weight,derivative_at_zero m k (by omega)]
    · rw [←iteratedDeriv_weight,derivative_at_one m k (by omega)]
  have h := polynomial_integration_by_parts 2 (densityPolynomial m) F hc hd hb
  apply Complex.ofReal_injective
  rw [←intervalIntegral.integral_ofReal,←intervalIntegral.integral_ofReal]
  push_cast
  simpa only [F,Nat.reduceSub,Function.iterate_succ_apply,Function.iterate_zero_apply,
    densityPolynomial_eval,iteratedDeriv_weight,neg_one_sq,one_mul] using h.symm
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.second_derivative_polynomial_pairing


