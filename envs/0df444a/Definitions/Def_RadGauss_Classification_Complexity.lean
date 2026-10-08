-- Prove2me | Definitions.Def_RadGauss_Classification_Complexity
-- name    : RadGauss_Classification_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:24:40.088231+00:00
-- url     : https://prove2.me/theorems/6de0b29c-360c-4558-971e-e7d66cc143e1
-- title:
--   Definition 2 — empirical Rademacher complexity R̂_n(F) and Rademacher complexity R_n(F), with factor 2/n and absolute value
-- statement:
--   Let $\mathcal X$ be a measurable space, $\mu$ a probability distribution on $\mathcal X$, $n \ge 1$ an integer and $F$ a class of functions $f : \mathcal X \to \mathbb R$. Let $\sigma_1, \dots, \sigma_n$ be independent uniform $\{\pm 1\}$-valued random variables. For a sample $x = (x_1, \dots, x_n) \in \mathcal X^n$ the **empirical Rademacher complexity** of $F$ is
--
--   $$\hat R_n(F)(x) = \mathbb E_\sigma\Big[\sup_{f \in F}\Big|\frac{2}{n}\sum_{i=1}^n \sigma_i f(x_i)\Big|\Big] = \frac{1}{2^n}\sum_{\sigma \in \{\pm1\}^n}\ \sup_{f \in F}\Big|\frac{2}{n}\sum_{i=1}^n \sigma_i f(x_i)\Big|,$$
--
--   and the **Rademacher complexity** of $F$ is its expectation over an i.i.d. sample $X_1, \dots, X_n \sim \mu$:
--
--   $$R_n(F) = \mathbb E\,\hat R_n(F)(X_1, \dots, X_n).$$
--
--   These are the complexity measures in which every risk bound of the paper is stated; note the factor $2/n$ and the absolute value inside the supremum.
--
--   **Formalization Note** Both quantities take values in $[0, \infty]$ (`ℝ≥0∞`): an unbounded class has complexity $+\infty$, and the supremum over the empty class is $0$. The expectation over the signs is the exact average over the $2^n$ sign vectors $\sigma : \mathrm{Fin}\,n \to \mathbb Z^\times$ ($\mathbb Z^\times = \{1, -1\}$, coerced to $\mathbb R$); the expectation over the sample is the lower Lebesgue integral against the product measure $\mu^n$. Sample indices are $0, \dots, n-1$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 464 (PDF p. 2), Definition 2

import Mathlib

open MeasureTheory

namespace RadGauss.Classification

/-- **Empirical Rademacher complexity** (Bartlett–Mendelson 2002, Definition 2, p. 464):
`R̂_n(F)(x) = E_σ [ sup_{f ∈ F} |(2/n) Σ_{i} σ_i f(x_i)| ]` for a sample `x = (x_1, …, x_n)`,
where `σ_1, …, σ_n` are independent uniform `{±1}`-valued random variables.
The expectation over `σ` is the exact average over all `2^n` sign vectors `σ : Fin n → ℤˣ`
(`ℤˣ = {1, -1}`, coerced to `ℝ`). The value lies in `ℝ≥0∞`, so an unbounded class has
complexity `⊤`, and the supremum over the empty class is `0`. -/
noncomputable def empiricalRademacher {X : Type*} (F : Set (X → ℝ)) (n : ℕ) (x : Fin n → X) :
    ENNReal :=
  (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
    ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, ((σ i : ℤ) : ℝ) * f (x i)|

/-- **Rademacher complexity** (Definition 2, p. 464): `R_n(F) = E R̂_n(F)`, the expectation of
the empirical Rademacher complexity over an i.i.d. sample `X_1, …, X_n ∼ μ`
(the product measure `μ^n`), as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def rademacherComplexity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (n : ℕ) (F : Set (X → ℝ)) : ENNReal :=
  ∫⁻ x, empiricalRademacher F n x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.Classification


