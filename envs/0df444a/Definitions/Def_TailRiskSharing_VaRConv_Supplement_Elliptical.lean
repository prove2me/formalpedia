-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Supplement_Elliptical
-- name    : TailRiskSharing_VaRConv_Supplement_Elliptical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:43:16.032425+00:00
-- url     : https://prove2.me/theorems/61b4336b-4047-48c7-a83a-50f9e96d5b88
-- title:
--   §7 — elliptical laws with a fixed characteristic generator
-- statement:
--   Fix a function $\psi:\mathbb R\to\mathbb C$. A measurable random vector $(X_1,\ldots,X_n)$ belongs to $\mathcal E_n(\psi)$ if there are a location $\mu\in\mathbb R^n$ and a symmetric positive semidefinite scatter matrix $\Sigma$ such that
--
--   $$\mathbb E[e^{i t^\top X}]=e^{i t^\top\mu}\psi(t^\top\Sigma t)\qquad(t\in\mathbb R^n).$$
--
--   The scalar class is the case $n=1$. Singular and zero scatter matrices are included. No density, moment, covariance identity or stochastic representation is imposed.
--
--   This is a characteristic-function definition of the general elliptical class, reusable independently of the allocation problem. The complex exponential has modulus one, so its expectation is integrable for measurable vectors on a probability space.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 22, §7

import Mathlib

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- §7 p.22: E_n(ψ), via its characteristic function, with fixed ψ.
The symmetric PSD scatter matrix may be singular or zero. No moments are required. -/
def IsElliptical (P : Measure Ω) (ψ : ℝ → ℂ) {n : ℕ}
    (Xs : Fin n → Ω → ℝ) : Prop :=
  (∀ i, Measurable (Xs i)) ∧
  ∃ μ : Fin n → ℝ, ∃ scatter : Matrix (Fin n) (Fin n) ℝ,
    scatter.IsSymm ∧ (∀ t : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, t i * scatter i j * t j) ∧
    ∀ t : Fin n → ℝ,
      (∫ ω, Complex.exp (Complex.I * ((∑ i, t i * Xs i ω : ℝ) : ℂ)) ∂P) =
        Complex.exp (Complex.I * ((∑ i, t i * μ i : ℝ) : ℂ)) *
          ψ (∑ i, ∑ j, t i * scatter i j * t j)

/-- §7 p.22: the scalar elliptical class E_1(ψ). -/
def IsEllipticalScalar (P : Measure Ω) (ψ : ℝ → ℂ) (X : Ω → ℝ) : Prop :=
  IsElliptical P ψ (fun _ : Fin 1 => X)

end TailRiskSharing.VaRConv.Supplement


