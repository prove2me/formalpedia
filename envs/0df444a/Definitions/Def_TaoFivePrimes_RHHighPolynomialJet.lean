-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
-- name    : TaoFivePrimes_RHHighPolynomialJet
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T06:31:07.721529+00:00
-- url     : https://prove2.me/theorems/c2129ef7-1938-4e07-994f-491026de81c8
-- title:
--   Normalized Taylor coefficients of the explicit Fourier polynomial
-- statement:
--   A transparent finite formula for normalized Taylor coefficients of the already defined Fourier polynomial, at any complex center and step. This defines a mathematical function only and makes no approximation, sign, zero count or RH assertion.
-- source:
--   Finite exponential-polynomial Taylor expansion. Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
set_option autoImplicit false
namespace RHHighPolynomialJet
open scoped ComplexConjugate
noncomputable def generator (m : Nat) : ℂ := ((2*Real.pi*(m:ℝ)/512:ℝ):ℂ)*Complex.I
noncomputable def jet (z h : ℂ) (k : Nat) : ℂ :=
 (if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)+
 ∑m∈Finset.range 1024,(RHHighFourierPolynomial.coefficient (m+1)*RHHighFourierPolynomial.phase (m+1) z*
    (generator (m+1)*h)^k/(k.factorial:ℂ)+
  conj (RHHighFourierPolynomial.coefficient (m+1))*RHHighFourierPolynomial.phase (m+1) (-z)*
    (-generator (m+1)*h)^k/(k.factorial:ℂ))
end RHHighPolynomialJet
noncomputable def TaoFivePrimes_RHHighPolynomialJet : Nat := 8


