-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
-- name    : TaoFivePrimes_RHHighFourierPolynomial
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T03:06:12.255237+00:00
-- url     : https://prove2.me/theorems/d7d8be4e-b7f4-40c7-a175-ef35aa5253c4
-- title:
--   Explicit real Fourier polynomial for the final high-height window
-- statement:
--   Transparent finite Fourier polynomial of period512 and bandwidth2, built from the proposed dyadic coefficients. This definition alone asserts no relationship to zeta, endpoint signs, zero count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaFourierData
set_option autoImplicit false
namespace RHHighFourierPolynomial
noncomputable def word (m : Nat) : Nat :=
  (((RHHighZetaFourierData.rows[m/512]?).getD [])[m%512]?).getD 0
noncomputable def realInteger (m : Nat) : Int := ((word m%2^96:Nat):Int)-2^95
noncomputable def imagInteger (m : Nat) : Int := ((word m/2^96%2^96:Nat):Int)-2^95
noncomputable def coefficient (m : Nat) : ℂ :=
  ((realInteger m:ℂ)+(imagInteger m:ℂ)*Complex.I)/(2:ℂ)^80
noncomputable def phase (m : Nat) (z : ℂ) : ℂ :=
  Complex.exp ((((2*Real.pi*(m:ℝ)/512:ℝ):ℂ)*Complex.I)*z)
noncomputable def polynomial (z : ℂ) : ℂ := coefficient 0+
  ∑ m∈Finset.range 1024, (coefficient (m+1)*phase (m+1) z+
    starRingEnd ℂ (coefficient (m+1))*phase (m+1) (-z))
end RHHighFourierPolynomial
noncomputable def TaoFivePrimes_RHHighFourierPolynomial : Nat := 1024


