-- Prove2me | Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
-- name    : DerivativeChainContinuation_Sixth9InversePolynomial
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T23:13:57.568195+00:00
-- url     : https://prove2.me/theorems/085ecc20-063c-4045-bde4-abc19af29764
-- title:
--   The cubic equation for the ninth-row inverse
-- statement:
--   For complex $t,w$, set
--
--   $$G_0(t)=4862-6864t+3003t^2-440t^3+15t^4,$$
--   $$G_1(t)=-3003+2145t-330t^2+6t^3,\qquad G_2(t)=330-60t,$$
--   $$G(t,w)=G_0(t)+G_1(t)w+G_2(t)w^2-2w^3.$$
--
--   These exact polynomials define the algebraic inverse equation; the later theorem constructs and validates the chosen root branch.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9InversePolynomial.lean#L4-L4; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9InversePolynomial.lean#L5-L5; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9InversePolynomial.lean#L6-L6; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9InversePolynomial.lean#L7-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
noncomputable def sixth9G0 (t : ℂ) : ℂ := 4862-6864*t+3003*t^2-440*t^3+15*t^4
noncomputable def sixth9G1 (t : ℂ) : ℂ := -3003+2145*t-330*t^2+6*t^3
noncomputable def sixth9G2 (t : ℂ) : ℂ := 330-60*t
noncomputable def sixth9G (t w : ℂ) : ℂ := sixth9G0 t+sixth9G1 t*w+sixth9G2 t*w^2-2*w^3
end DerivativeChainContinuation


