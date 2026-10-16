-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
-- name    : TaoFivePrimes_RHBatch01FourierPolynomial
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:03:57.966185+00:00
-- url     : https://prove2.me/theorems/17568fa6-f800-434b-99e9-44d8b8f9a44c
-- title:
--   Explicit real Fourier polynomial for the final high-height window
-- statement:
--   Transparent finite Fourier polynomial of period512 and bandwidth2, built from the proposed dyadic coefficients. This definition alone asserts no relationship to zeta, endpoint signs, zero count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaFourierData
set_option autoImplicit false
namespace RHBatch01FourierPolynomial
noncomputable def word (m : Nat) : Nat :=
  (((RHBatch01ZetaFourierData.rows[m/512]?).getD [])[m%512]?).getD 0
noncomputable def realInteger (m : Nat) : Int := ((word m%2^96:Nat):Int)-2^95
noncomputable def imagInteger (m : Nat) : Int := ((word m/2^96%2^96:Nat):Int)-2^95
noncomputable def coefficient (m : Nat) : ℂ :=
  ((realInteger m:ℂ)+(imagInteger m:ℂ)*Complex.I)/(2:ℂ)^80
noncomputable def phase (m : Nat) (z : ℂ) : ℂ :=
  Complex.exp ((((2*Real.pi*(m:ℝ)/512:ℝ):ℂ)*Complex.I)*z)
noncomputable def polynomial (z : ℂ) : ℂ := coefficient 0+
  ∑ m∈Finset.range 1024, (coefficient (m+1)*phase (m+1) z+
    starRingEnd ℂ (coefficient (m+1))*phase (m+1) (-z))
end RHBatch01FourierPolynomial
noncomputable def TaoFivePrimes_RHBatch01FourierPolynomial : Nat := 1024


