-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
-- name    : TaoFivePrimes_RHHighSamplingFunctions
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T03:18:06.301886+00:00
-- url     : https://prove2.me/theorems/f491a8a1-b101-4a3f-bed4-9767ada36cd6
-- title:
--   Analytic gamma sampling functions for the Platt Fourier method
-- statement:
--   Transparent definitions of the Gaussian-windowed gamma function, factorial-normalized moments, centered sampling grid and chirped samples. No approximation, sign, count or RH statement is asserted.
-- source:
--   Platt DOI10.1090/mcom/3198, windowed Fourier/Taylor reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
set_option autoImplicit false
namespace RHHighSamplingFunctions
noncomputable def sampleIndex (i : Nat) : Int := (i:Int)-8192
noncomputable def sampleTime (i : Nat) : ℝ := (sampleIndex i:ℝ)/32
noncomputable def gammaWindow (T t : ℝ) : ℂ :=
  Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))
noncomputable def moment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  (gammaWindow T t*(-2*(Real.pi:ℂ)*Complex.I*(t:ℂ))^k)/
    ((k.factorial:ℂ)*(512:ℂ)^k)
noncomputable def chirpedSample (T : ℝ) (k i : Nat) : ℂ :=
  moment T k (sampleTime i)*Complex.exp (((-Real.pi*(i:ℝ)^2/16384:ℝ):ℂ)*Complex.I)
end RHHighSamplingFunctions
noncomputable def TaoFivePrimes_RHHighSamplingFunctions : Nat := 16384


