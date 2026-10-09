-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LogTailAnalytic
-- name    : OAI_NumberTheory_PiExponent_Analysis_LogTailAnalytic
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:42:11.020296+00:00
-- url     : https://prove2.me/theorems/546a529c-9106-4e47-b553-08a191bc6626
-- title:
--   Complex logarithm truncation tail and series identities
-- statement:
--   For T : ℕ and z : ℂ, logTail T z is Complex.logTaylor T z − Complex.log (1 + z). The bundle also identifies the convergent power-series coefficient sum for Complex.log (1 + z) when ‖z‖ < 1, and gives general HasSum rules for coefficients of products, the constant series 1, and powers of a power series.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogTailAnalytic.lean#L11-L176

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix



namespace OAI

open scoped BigOperators

namespace PiExponent.LogTailAnalytic

noncomputable def logTail (T : ℕ) (z : ℂ) : ℂ :=
  Complex.logTaylor T z - Complex.log (1 + z)





 













theorem hasSum_formal_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
      (Complex.log (1 + z)) := by
  convert Complex.hasSum_taylorSeries_log hz using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]
    ring







theorem hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  convert hs using 1 <;> try rfl
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
  rw [← he, pow_add]
  ring

theorem hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

 theorem hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using hasSum_coeff_mul hd hf











end PiExponent.LogTailAnalytic

end OAI


