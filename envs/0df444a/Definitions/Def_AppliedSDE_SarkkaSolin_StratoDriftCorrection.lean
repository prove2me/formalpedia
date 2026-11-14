-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_StratoDriftCorrection
-- name    : AppliedSDE_SarkkaSolin_StratoDriftCorrection
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T17:50:22.244759+00:00
-- url     : https://prove2.me/theorems/abafd144-6fbc-477d-829d-56fc0698e5f3
-- title:
--   Multidimensional Stratonovich-to-Itô drift correction
-- statement:
--   Algorithm 4.11, equation (4.55), defines the corrected Itô drift by adding one half of the dispersion Jacobian contracted against the dispersion columns. This is a source-exact algebraic formula for a multivariate state and Brownian driving vector. The Stratonovich integral and proof of stochastic equivalence are separate and remain an open formalisation obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   b_i^{\mathrm{Ito}}=b_i^{\mathrm{Strat}}+\frac12\sum_{j,k}\sigma_{jk}\,\partial_j\sigma_{ik}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 4.11, Equation (4.55), printed p. 56. https://doi.org/10.1017/9781108186735

import Mathlib
set_option autoImplicit false
open scoped BigOperators

namespace AppliedSDE.SarkkaSolin

/-- Särkkä–Solin Algorithm 4.11, Eq. (4.55): the multidimensional
Stratonovich-to-Itô drift correction. The stochastic equivalence of the
integrals is a separate theorem requiring a real Stratonovich integral. -/
noncomputable def stratonovichCorrectedDrift
    {n m : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ)
    (L : (Fin n → ℝ) → Fin n → Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  f x i + (1 / 2 : ℝ) *
    ∑ j : Fin m, ∑ l : Fin n,
      fderiv ℝ (fun y : Fin n → ℝ => L y i j) x
        (Pi.single l (1 : ℝ)) * L x l j

end AppliedSDE.SarkkaSolin


