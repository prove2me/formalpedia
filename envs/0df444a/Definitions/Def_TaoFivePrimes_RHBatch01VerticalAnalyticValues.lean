-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01VerticalAnalyticValues
-- name    : TaoFivePrimes_RHBatch01VerticalAnalyticValues
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:57:49.908279+00:00
-- url     : https://prove2.me/theorems/0eea33f4-ab43-4716-afcd-4f95d49d468c
-- title:
--   Actual finite center Taylor sums for the vertical contour edges
-- statement:
--   Ordinary mathematical functions for actual Fourier polynomial coefficients times exact eighth roots, real vertical frequencies, factorial Taylor terms and the finite1024-frequency center sum. No numerical accuracy, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourAnalyticValues
set_option autoImplicit false
open Complex
namespace RHBatch01VerticalAnalyticValues
noncomputable def seed (t : Fin 3) (positive : Bool) (m : Nat) : ℂ :=
 RHBatch01ContourAnalyticValues.trueCoefficient m positive*
 RHBatch01ContourAnalyticValues.exactUnit (RHBatch01ContourCoefficientData.rootIndex t positive m)
noncomputable def frequency (positive : Bool) (m : Nat) : ℂ :=
 (((if positive then (-1:ℝ) else 1)*Real.pi*(m:ℝ)/512:ℝ):ℂ)
noncomputable def term (t : Fin 3) (positive : Bool) (m n : Nat) : ℂ :=
 seed t positive m*frequency positive m^n/(n.factorial:ℂ)
noncomputable def center (t : Fin 3) (n : Nat) : ℂ :=
 (if n=0 then RHBatch01FourierPolynomial.coefficient 0 else 0)+
 ∑m:Fin 1024,(term t true (m.val+1) n+term t false (m.val+1) n)
end RHBatch01VerticalAnalyticValues
noncomputable def TaoFivePrimes_RHBatch01VerticalAnalyticValues : Nat := 55


