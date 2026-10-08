-- Prove2me | Definitions.Def_RadGauss_Kernel_Complexity
-- name    : RadGauss_Kernel_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:38.970357+00:00
-- url     : https://prove2.me/theorems/7fc433a0-dfef-47fc-9573-adb2c3865a00
-- title:
--   Definition 2 — empirical Gaussian complexity Ĝ_n(F), with factor 2/n and absolute value
-- statement:
--   Let $F$ be a class of functions from $\mathcal X$ to $\mathbb R$, let $x=(x_1,\dots,x_n)$ be a fixed sample, and let $g_1,\dots,g_n$ be independent standard Gaussian random variables. Definition 2's empirical Gaussian complexity is
--
--   $$\hat G_n(F)(x)=\mathbb E_g\Big[\sup_{f\in F}\Big|\frac{2}{n}\sum_{i=1}^n g_i f(x_i)\Big|\Big].$$
--
--   This quantity is used in the sample-wise Gaussian half of Lemma 22. The expected Gaussian complexity and both Rademacher complexities are supplied by the shared definitions referenced earlier in this mission.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (`ℝ≥0∞`). The Gaussian vector has product law $N(0,1)^{\otimes n}$ on $\mathrm{Fin}\,n\to\mathbb R$, and the expectation is a lower Lebesgue integral. Sample indices are $0,\dots,n-1$; at $n=0$ the sum and complexity are $0$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 464 (PDF p. 2), Definition 2

import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadGauss.Kernel

/-- **Empirical Gaussian complexity** (Definition 2, p. 464):
`Ĝ_n(F)(x) = E[ sup_{f ∈ F} |(2/n) Σ_{i=1}^n g_i f(x_i)| | x_1, …, x_n ]`, where
`g_1, …, g_n` are independent standard Gaussian `N(0,1)` variables. The Gaussian vector is the
coordinate vector of the product measure `N(0,1)^{⊗n}` on `Fin n → ℝ`, and the expectation is a
lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def empiricalGaussian {X : Type*} (F : Set (X → ℝ)) (n : ℕ) (x : Fin n → X) :
    ℝ≥0∞ :=
  ∫⁻ g : Fin n → ℝ, ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, g i * f (x i)|
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

end RadGauss.Kernel


