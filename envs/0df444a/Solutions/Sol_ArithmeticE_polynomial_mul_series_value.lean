-- Prove2me | solution 1 for ArithmeticE.polynomial_mul_series_value
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:42:35.221681+00:00
-- url     : https://prove2.me/submissions/5c16fcb2-a8d8-4632-ac39-f8a2471a4d0b

import Definitions.Def_rationalEArithmetic
import Theorems.Thm_ArithmeticE_series_summable
open ArithmeticE Polynomial
namespace BeukersEvaluation
lemma polynomial_series_summable (P : Polynomial ℂ) (z : ℂ) :
    Summable (fun n => P.coeff n * z^n) := by
  apply summable_of_ne_finset_zero (s := P.support)
  intro n hn
  simp [notMem_support_iff.mp hn]

lemma polynomial_value (P : Polynomial ℂ) (z : ℂ) :
    (∑' n, P.coeff n * z^n) = P.eval z := by
  rw [tsum_eq_sum (s := P.support)]
  · exact (eval_eq_sum).symm
  · intro n hn
    simp [notMem_support_iff.mp hn]

lemma polynomial_mul_value (P : Polynomial ℂ) (f : PowerSeries ℂ)
    (hf : RationalSeriesArithmetic f) (z : ℂ) :
    seriesValue ((P : PowerSeries ℂ)*f) z = P.eval z * seriesValue f z := by
  have hp := polynomial_series_summable P z
  have hs := ArithmeticE.series_summable f hf z
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hp.norm hs.norm
  rw [polynomial_value] at hprod
  simp only [seriesValue]
  rw [hprod]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hn : k.1 + k.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
  simp only [Polynomial.coeff_coe]
  rw [← hn, pow_add]
  ring
end BeukersEvaluation


theorem solution (P : Polynomial ℂ) (f : PowerSeries ℂ)
    (hf : RationalSeriesArithmetic f) (z : ℂ) :
    seriesValue ((P : PowerSeries ℂ)*f) z = P.eval z * seriesValue f z := by
  exact BeukersEvaluation.polynomial_mul_value P f hf z
#print axioms solution
