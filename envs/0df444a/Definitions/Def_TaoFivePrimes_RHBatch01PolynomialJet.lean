-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
-- name    : TaoFivePrimes_RHBatch01PolynomialJet
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:29:52.485819+00:00
-- url     : https://prove2.me/theorems/2f720f0e-41da-4ff7-ad49-d9a49adbc8dc
-- title:
--   Normalized Taylor coefficients of the explicit Fourier polynomial
-- statement:
--   A transparent finite formula for normalized Taylor coefficients of the already defined Fourier polynomial, at any complex center and step. This defines a mathematical function only and makes no approximation, sign, zero count or RH assertion.
-- source:
--   Finite exponential-polynomial Taylor expansion. Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
set_option autoImplicit false
namespace RHBatch01PolynomialJet
open scoped ComplexConjugate
noncomputable def generator (m : Nat) : ℂ := ((2*Real.pi*(m:ℝ)/512:ℝ):ℂ)*Complex.I
noncomputable def jet (z h : ℂ) (k : Nat) : ℂ :=
 (if k=0 then RHBatch01FourierPolynomial.coefficient 0 else 0)+
 ∑m∈Finset.range 1024,(RHBatch01FourierPolynomial.coefficient (m+1)*RHBatch01FourierPolynomial.phase (m+1) z*
    (generator (m+1)*h)^k/(k.factorial:ℂ)+
  conj (RHBatch01FourierPolynomial.coefficient (m+1))*RHBatch01FourierPolynomial.phase (m+1) (-z)*
    (-generator (m+1)*h)^k/(k.factorial:ℂ))
end RHBatch01PolynomialJet
noncomputable def TaoFivePrimes_RHBatch01PolynomialJet : Nat := 8


