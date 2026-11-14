-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreMassPolynomial
-- name    : row23_rh_supp_RHLegendreMassPolynomial
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:52.712884+00:00
-- url     : https://prove2.me/theorems/af27cdfc-2cf7-4511-b57c-dea3d25cccce
-- title:
--   Row 23 RH support: RHLegendreMassPolynomial
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRodrigues
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial Finset MeasureTheory intervalIntegral
noncomputable def rationalMassPolynomial (m : ℕ) (δ : ℚ) : ℚ[X] :=
  (shiftedLegendre m).map (Int.castRingHom ℚ)*(1+C δ*X)^(m+1)
lemma rationalMassPolynomial_eval (m : ℕ) (δ : ℚ) (t : ℝ) :
    ((rationalMassPolynomial m δ).map (Rat.castHom ℝ)).eval t=
      ((shiftedLegendre m).map (Int.castRingHom ℝ)).eval t*(1+(δ:ℝ)*t)^(m+1) := by
  simp only [rationalMassPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_add,Polynomial.map_one,Polynomial.map_C,Polynomial.map_X,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_one,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.map_map]
  congr 2
 theorem derivativeMass_rational_polynomial (m : ℕ) (δ : ℚ) (hδ : 0 ≤ δ) :
    derivativeMass m (δ:ℝ)=((2*m+1).factorial:ℝ)/(m.factorial:ℝ)*
      (∫ t : ℝ in 0..1, |((rationalMassPolynomial m δ).map (Rat.castHom ℝ)).eval t|) := by
  rw [derivativeMass_eq]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Set.Icc (0:ℝ) 1 by simpa using ht).1
  have hδr : (0:ℝ) ≤ δ := by exact_mod_cast hδ
  dsimp only
  rw [rationalMassPolynomial_eval,abs_mul,abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ 1+(δ:ℝ)*t) (m+1))]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.rationalMassPolynomial_eval
#print axioms DusartLegendreSmoothing.derivativeMass_rational_polynomial


