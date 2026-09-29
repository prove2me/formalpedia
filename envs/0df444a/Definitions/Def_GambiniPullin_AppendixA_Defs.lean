-- Prove2me | Definitions.Def_GambiniPullin_AppendixA_Defs
-- name    : GambiniPullin_AppendixA_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T13:52:07.64499+00:00
-- url     : https://prove2.me/theorems/098fab62-6822-4eb0-ba4d-b00bd00b8e88
-- title:
--   Gambini–Pullin Appendix A: model integrals (A.1), (A.2)
-- statement:
--   Definitions for the model integrals of Appendix A. For real $\sigma, x, y$: $D_\sigma(x,y) = 1 + x^2 + y^2/(1+\sigma y^2)$ (`modelDenom`); $f_\sigma(x,y) = (x^2-y^2)/D_\sigma(x,y)^2$ (`modelIntegrand`, the integrand of (A.1)); $I^{\mathrm{disk}}_\sigma(R) = \int_{x^2+y^2\le R^2} f_\sigma$ (`diskModelIntegral`, a rotation-invariant truncation of (A.1)); $e^{-\alpha x^2}e^{-\beta(x^2+y^2)}f_\sigma(x,y)$ (`weightedModelIntegrand`, the integrand of (A.2)); and $I(\alpha,\beta,\sigma) = \int_{\mathbb R^2} e^{-\alpha x^2}e^{-\beta(x^2+y^2)}f_\sigma$ (`weightedModelIntegral`, eq. (A.2)).
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, eqs. (A.1), (A.2).

import Mathlib

/-!
# Gambini–Pullin (2014), Appendix A: model integrals

Definitions for the two-dimensional model integrals (A.1) and (A.2) of
R. Gambini and J. Pullin, *Emergence of stringlike physics from Lorentz invariance
in loop quantum gravity*, Int. J. Mod. Phys. D 23 (2014) 1442023, Appendix A.
-/

namespace GambiniPullin

/-- The denominator base of (A.1): `1 + x² + y² / (1 + σ y²)`. -/
noncomputable def modelDenom (σ x y : ℝ) : ℝ :=
  1 + x ^ 2 + y ^ 2 / (1 + σ * y ^ 2)

/-- The integrand of (A.1): `(x² - y²) / (1 + x² + y² / (1 + σ y²))²`. -/
noncomputable def modelIntegrand (σ x y : ℝ) : ℝ :=
  (x ^ 2 - y ^ 2) / (modelDenom σ x y) ^ 2

/-- The integral (A.1) truncated to the closed Euclidean disk `x² + y² ≤ R²`
(a rotation-invariant regularization of the formal integral (A.1)). -/
noncomputable def diskModelIntegral (σ R : ℝ) : ℝ :=
  ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2}, modelIntegrand σ p.1 p.2

/-- The integrand of (A.2): `e^{-α x²} e^{-β (x² + y²)} (x² - y²) / (1 + x² + y²/(1+σy²))²`. -/
noncomputable def weightedModelIntegrand (α β σ x y : ℝ) : ℝ :=
  Real.exp (-α * x ^ 2) * Real.exp (-β * (x ^ 2 + y ^ 2)) * modelIntegrand σ x y

/-- The weighted integral (A.2) over the whole plane `ℝ²` (Lebesgue measure). -/
noncomputable def weightedModelIntegral (α β σ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, weightedModelIntegrand α β σ p.1 p.2

end GambiniPullin


