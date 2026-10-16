-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourAnalyticValues
-- name    : TaoFivePrimes_RHBatch01ContourAnalyticValues
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:10:17.698976+00:00
-- url     : https://prove2.me/theorems/70827e73-2df7-44fa-9be4-02f938607d83
-- title:
--   Exact analytic values used by the contour Taylor algorithm
-- statement:
--   Explicit mathematical functions: exact eighth roots of unity, Fourier coefficients, real exponential amplitudes, frequencies, seeds and normalized Taylor terms. Contains no approximation, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace RHBatch01ContourAnalyticValues
open RHBatch01ContourCoefficientData
noncomputable def exactUnit (j : Nat) : ℂ := match j%8 with
  | 0 => 1
  | 1 => (Real.sqrt 2:ℂ)/2+((Real.sqrt 2:ℂ)/2)*I
  | 2 => I
  | 3 => -(Real.sqrt 2:ℂ)/2+((Real.sqrt 2:ℂ)/2)*I
  | 4 => -1
  | 5 => -(Real.sqrt 2:ℂ)/2-((Real.sqrt 2:ℂ)/2)*I
  | 6 => -I
  | _ => (Real.sqrt 2:ℂ)/2-((Real.sqrt 2:ℂ)/2)*I
noncomputable def trueCoefficient (m : Nat) (positive : Bool) : ℂ :=
  if positive then RHBatch01FourierPolynomial.coefficient m else conj (RHBatch01FourierPolynomial.coefficient m)
noncomputable def trueAmplitude (m : Nat) (positive : Bool) : ℝ :=
  Real.exp ((if positive then -1 else 1)*Real.pi*(m:ℝ)/512)
noncomputable def trueFrequency (m : Nat) (positive : Bool) : ℂ :=
  ((if positive then (1:ℝ) else -1)*Real.pi*(m:ℝ)/8192:ℝ)*I
noncomputable def trueSeed (t : Fin 3) (positive : Bool) (m : Nat) : ℂ :=
  trueCoefficient m positive*exactUnit (rootIndex t positive m)*
    (trueAmplitude m positive:ℂ)
noncomputable def trueTerm (t : Fin 3) (positive : Bool) (m k : Nat) : ℂ :=
  trueSeed t positive m*(trueFrequency m positive)^k/(k.factorial:ℂ)
end RHBatch01ContourAnalyticValues
noncomputable def TaoFivePrimes_RHBatch01ContourAnalyticValues : Nat := 8


