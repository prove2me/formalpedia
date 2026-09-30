-- Prove2me | Definitions.Def_XuMannorRobust_Quantile_LossQuantile
-- name    : XuMannorRobust_Quantile_LossQuantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:07:45.461204+00:00
-- url     : https://prove2.me/theorems/a9d91407-a768-46a2-a64b-281c49efa807
-- title:
--   Quantile value $\mathcal Q(h,\beta,\mu)$, truncated mean $\mathcal T(h,\beta,\mu)$ of the loss, and the empirical distribution $\mu_{\mathrm{emp}}$
-- statement:
--   Let $\mathcal Z$ be a measurable space of samples, $\mathcal H$ a set of hypotheses and $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss. For a hypothesis $h$, a level $\beta$ and a measure $\nu$ on $\mathcal Z$, set
--
--   $$\mathcal Q(h, \beta, \nu) = \mathbb Q^\beta\big(l(h, z)\big), \qquad \mathcal T(h, \beta, \nu) = \mathbb T^\beta\big(l(h, z)\big), \qquad z \sim \nu,$$
--
--   the $\beta$-quantile value and $\beta$-truncated mean of the (random) testing error of $h$ when the test sample follows $\nu$. For a training set $\mathbf s = (s_1, \dots, s_n)$ the **empirical distribution** is
--
--   $$\mu_{\mathrm{emp}} = \frac1n \sum_{i=1}^n \delta_{s_i},$$
--
--   so that $\mathcal Q(h, \beta, \mu_{\mathrm{emp}})$ and $\mathcal T(h, \beta, \mu_{\mathrm{emp}})$ are the empirical quantile and truncated mean of the training losses.
--
--   These are the quantities compared in Theorems 2 and 5 of Xu and Mannor: population quantities under the sample distribution $\mu$ against empirical ones under $\mu_{\mathrm{emp}}$.
--
--   **Formalization Note** The law of $l(h, z)$ is the push-forward `ν.map (l h)`; every theorem assumes each $l(h,\cdot)$ measurable. $\mathbb T^\beta$ is the corrected Definition 3 (see that definition). The empirical distribution is $n^{-1}$ times a sum of Dirac masses, a probability measure for $n \ge 1$; repeated sample points accumulate mass.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 400 (definitions of Q(h, β, μ) and T(h, β, μ)); p. 400 Theorem 2 and p. 402 Theorem 5 (empirical distribution μ_emp)

import Mathlib
import Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean

open MeasureTheory

namespace XuMannorRobust.Quantile

/-- **Quantile value of the testing error** (Xu & Mannor 2012, p. 400):
`Q(h, β, ν) = ℚ^β(l(h, z))` with `z ∼ ν`, i.e. the β-quantile value of the law of `l(h, ·)`
under `ν` (the push-forward `ν.map (l h)`). -/
noncomputable def lossQuantile {Z H : Type*} [MeasurableSpace Z] (l : H → Z → ℝ) (h : H)
    (β : ℝ) (ν : Measure Z) : ℝ :=
  quantileValue (ν.map (l h)) β

/-- **Truncated mean of the testing error** (Xu & Mannor 2012, p. 400):
`T(h, β, ν) = 𝕋^β(l(h, z))` with `z ∼ ν`, the β-truncated mean (Definition 3, corrected second
branch) of the law of `l(h, ·)` under `ν`. -/
noncomputable def lossTruncatedMean {Z H : Type*} [MeasurableSpace Z] (l : H → Z → ℝ) (h : H)
    (β : ℝ) (ν : Measure Z) : ℝ :=
  truncatedMean (ν.map (l h)) β

/-- **Empirical distribution** `μ_emp` of a training set `s = (s_1, …, s_n)` (Xu & Mannor 2012,
p. 400, Theorem 2; p. 402, Theorem 5): the measure putting mass `1/n` on each sample point,
`μ_emp = (1/n) ∑_i δ_{s_i}` (repeated points accumulate mass). A probability measure for `n ≥ 1`. -/
noncomputable def empiricalMeasure {Z : Type*} [MeasurableSpace Z] {n : ℕ} (s : Fin n → Z) :
    Measure Z :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (s i)

end XuMannorRobust.Quantile


