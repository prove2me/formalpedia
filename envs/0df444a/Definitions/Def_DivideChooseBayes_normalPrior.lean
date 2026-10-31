-- Prove2me | Definitions.Def_DivideChooseBayes_normalPrior
-- name    : DivideChooseBayes_normalPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:14.325403+00:00
-- url     : https://prove2.me/theorems/dc223004-c52b-4eb8-96a4-b584a9e40699
-- title:
--   Independent normal priors $\prod_i \mathcal N(\mu_i,\sigma_i^2)$
-- statement:
--   Under **normal priors** the chooser's value for good $i$ is drawn from $\mathcal N(\mu_i,\sigma_i)$, with mean $\mu_i\in\mathbb R$ and **standard deviation** $\sigma_i>0$, independently across goods. The prior is the product measure
--
--   $$\bigotimes_{i=1}^n \mathcal N(\mu_i,\sigma_i^2)$$
--
--   on $\mathbb R^n$ (normal laws written with their variance).
--
--   **Formalization Note** Mathlib's `gaussianReal m v` takes the variance $v=\sigma_i^2$. The positivity $\sigma_i>0$ is a hypothesis of every theorem that uses this prior.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5 ("Normal priors"); Algorithm 1, p.9 ("independent normal priors")

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Independent normal priors.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5: "Normal priors: The value for good each i is drawn from N(µᵢ, σᵢ) for some mean
µᵢ ∈ ℝ and standard deviation σᵢ > 0."; Algorithm 1 (p.9) assumes "independent normal priors".

The product over goods of the normal laws `N(mᵢ, σᵢ²)`: the law of the chooser's values.

**Formalization Note.** `σᵢ` is a standard deviation; Mathlib's `gaussianReal m v` takes the
variance `v = σᵢ²`. Independence across goods is the product measure `Measure.pi`. The positivity
`σᵢ > 0` is a hypothesis of every theorem that uses this prior. -/
noncomputable def normalPrior {ι : Type*} [Fintype ι] (m σ : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi fun i => gaussianReal (m i) (σ i ^ 2).toNNReal

end DivideChooseBayes


