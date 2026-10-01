-- Prove2me | Definitions.Def_Zeta5_MomentWeight
-- name    : Zeta5_MomentWeight
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T10:37:15.285681+00:00
-- url     : https://prove2.me/theorems/d6f2c34a-f9e2-4976-b72d-b1f01ffb9852
-- title:
--   Zeta5: moment weight and rational integrands
-- statement:
--   For every real $y$, define
--   $$w(y)=\frac{(2\pi)^4y^5}{12}\sum_{\ell=1}^{\infty}\ell^4e^{-2\pi\ell y}.$$
--   For a natural number $K$ and a rational polynomial $P$, define
--   $$J_{K,P}(y)=\frac{P(y^2)}{D_K(y^2)}w(y).$$
--   These are total real functions. Convergence of the series, integrability, and positivity on $(0,\infty)$ are mathematical results, not fields assumed in the definitions. The expressions are exactly those in the source's weight and positivity modules; subsequent statements use Lebesgue integrals over $(0,\infty)$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Weight.lean#L14-L19; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Positivity.lean#L49-L51

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction

open Polynomial

namespace Apery

noncomputable def wS (y : ℝ) : ℝ :=
  ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))

noncomputable def w (y : ℝ) : ℝ := (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y

noncomputable def integrand (K : ℕ) (P : ℚ[X]) (y : ℝ) : ℝ :=
  aeval (y ^ 2) P / aeval (y ^ 2) (D K) * w y

end Apery


