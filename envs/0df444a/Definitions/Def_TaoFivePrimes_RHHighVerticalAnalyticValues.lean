-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighVerticalAnalyticValues
-- name    : TaoFivePrimes_RHHighVerticalAnalyticValues
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T09:37:02.668332+00:00
-- url     : https://prove2.me/theorems/00167faa-2264-4d4f-9025-42b7b5640883
-- title:
--   Actual finite center Taylor sums for the vertical contour edges
-- statement:
--   Ordinary mathematical functions for actual Fourier polynomial coefficients times exact eighth roots, real vertical frequencies, factorial Taylor terms and the finite1024-frequency center sum. No numerical accuracy, nonvanishing, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourAnalyticValues
set_option autoImplicit false
open Complex
namespace RHHighVerticalAnalyticValues
noncomputable def seed (t : Fin 3) (positive : Bool) (m : Nat) : ℂ :=
 RHHighContourAnalyticValues.trueCoefficient m positive*
 RHHighContourAnalyticValues.exactUnit (RHHighContourCoefficientData.rootIndex t positive m)
noncomputable def frequency (positive : Bool) (m : Nat) : ℂ :=
 (((if positive then (-1:ℝ) else 1)*Real.pi*(m:ℝ)/512:ℝ):ℂ)
noncomputable def term (t : Fin 3) (positive : Bool) (m n : Nat) : ℂ :=
 seed t positive m*frequency positive m^n/(n.factorial:ℂ)
noncomputable def center (t : Fin 3) (n : Nat) : ℂ :=
 (if n=0 then RHHighFourierPolynomial.coefficient 0 else 0)+
 ∑m:Fin 1024,(term t true (m.val+1) n+term t false (m.val+1) n)
end RHHighVerticalAnalyticValues
noncomputable def TaoFivePrimes_RHHighVerticalAnalyticValues : Nat := 55


