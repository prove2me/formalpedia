-- Prove2me | Definitions.Def_MeanOnlyProphet_prophetMean
-- name    : MeanOnlyProphet_prophetMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:06.188909+00:00
-- url     : https://prove2.me/theorems/ac9997cf-c19b-4786-ab96-0364af70b72a
-- title:
--   Expected maximum $\mathbb E[X^*]$ of $n$ i.i.d. values
-- statement:
--   Let $\mu$ be a probability law on $\mathbb R$ and $n\ge1$. Let $X_1,\dots,X_n$ be independent with common law $\mu$ and write $X^*=\max_{1\le i\le n}X_i$. The **prophet's benchmark** is
--   $$
--   \mathbb E[X^*]=\int_{\mathbb R^n}\max_{1\le i\le n}x_i\;d\mu^{\otimes n}(x).
--   $$
--   It is the reward of a prophet who sees all realizations, and the only statistic of the law that the mean-only algorithm is given.
--
--   **Formalization Note** The values are the coordinates of $x\in\mathbb R^{n}$ (`Fin n → ℝ`) under the product law `Measure.pi (fun _ => μ)`; the maximum is the published `SamuelCahnProphet.Median.maxX`. The expectation is a Bochner integral, which equals $\mathbb E[X^*]$ whenever $\mu$ has a finite mean.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

open MeasureTheory

namespace MeanOnlyProphet

/-- **The prophet's benchmark `E[X*]` for `n` i.i.d. values.** Feng, Jin, Wu, Xiang, *Mean-only
Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §2, p.5 (PDF p.6):
"Let X1, . . . , Xn be independent nonnegative random variables. Write X∗ = max1≤i≤n {Xi}. …
In the i.i.d. setting, the variables have the same distribution."

`prophetMean μ n = ∫ max_i x_i d(μ^⊗n)(x)`, the expected maximum of `n` independent draws from `μ`.

**Formalization Note.** The values are the coordinates of `x : Fin n → ℝ` under the product law
`Measure.pi (fun _ => μ)`; the maximum is the published `SamuelCahnProphet.Median.maxX` applied to the
coordinate projections. The expectation is a Bochner integral: it is the true `E[X*]` whenever `μ`
has a finite mean (statements using it assume this or `E[X*] = 1`). `n ≥ 1` is the instance `NeZero n`. -/
noncomputable def prophetMean (μ : Measure ℝ) (n : ℕ) [NeZero n] : ℝ :=
  ∫ x, SamuelCahnProphet.Median.maxX (fun (i : Fin n) (y : Fin n → ℝ) => y i) x
    ∂(Measure.pi fun _ : Fin n => μ)

end MeanOnlyProphet


