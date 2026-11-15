-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_PolynomialData
-- name    : BooleanHiddenPartition_LowerBounds_Supplement_PolynomialData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:14:31.794212+00:00
-- url     : https://prove2.me/theorems/5bab7f13-60e3-49c7-acfb-f93d89d78e90
-- title:
--   Polynomial evaluation, Fourier spectral norm and margin
-- statement:
--   Let $p$ be a real polynomial in $k$ variables, and let $g_p$ be its restriction to the sign cube. Under the published Boolean encoding, true denotes $-1$ and false denotes $+1$. Define its Fourier spectral norm and margin by
--
--   $$g_p(z)=p(z),\qquad
--   \|\widehat p\|_1=\sum_{T\subseteq[k]}|\mathbb E_z[g_p(z)\chi_T(z)]|,\qquad
--   \beta(p)=\min_{z\in\{\pm1\}^k}|g_p(z)|.$$
--
--   The expectation is uniform over all $2^k$ cube points. The spectral norm is the referenced general spectral norm, applied to $g_p$; it is not the sum of absolute values of formal polynomial coefficients. The minimum is taken over a finite nonempty cube, including its singleton at $k=0$. If $p$ strictly sign-represents a Boolean function, every absolute value in this minimum is positive. These are computed quantities, with no communication bound built into them.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, Characterizing Quantum Advantage for Generalizations of the Boolean Hidden Matching Problem, STOC 2027 submission #1085 (October 2026), p. 14, Norms; p. 25, Theorem 12 and Fourier expansion

import Definitions.Def_BooleanHiddenPartition_LowerBounds_SignDegree
import Definitions.Def_FourierEntropyApprox_fourierCoeff

open scoped BigOperators
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds.Supplement

noncomputable section

/-- Evaluation at the published ±1 encoding, with true mapped to -1. -/
def polyOnCube {k : ℕ} (p : MvPolynomial (Fin k) ℝ) (z : Cube k) : ℝ :=
  MvPolynomial.eval (fun j => sign (z j)) p

/-- Fourier ℓ₁ norm of the evaluated cube function, with uniform normalization.
This is not the sum of absolute values of formal polynomial coefficients. -/
def polyFourierL1 {k : ℕ} (p : MvPolynomial (Fin k) ℝ) : ℝ :=
  FourierEntropyApprox.spectralNorm (polyOnCube p)

/-- The actual finite minimum, on the nonempty cube (also when k = 0). -/
def polyMargin {k : ℕ} (p : MvPolynomial (Fin k) ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun z : Cube k => |polyOnCube p z|)

end

end BooleanHiddenPartition.LowerBounds.Supplement


