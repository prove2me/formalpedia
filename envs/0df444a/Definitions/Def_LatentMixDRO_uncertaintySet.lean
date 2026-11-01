-- Prove2me | Definitions.Def_LatentMixDRO_uncertaintySet
-- name    : LatentMixDRO_uncertaintySet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:44.835022+00:00
-- url     : https://prove2.me/theorems/e4f9fa20-1f7a-4c6f-ad3a-3d273c302427
-- title:
--   Potential minority subpopulations $\mathcal P_{\alpha_0,X}$
-- statement:
--   For a law $P_X$ of the covariates and $\alpha_0\in(0,\tfrac12)$, the **set of potential minority subpopulations** is
--
--   $$
--   \mathcal P_{\alpha_0,X}=\big\{Q_0: P_X=\alpha Q_0+(1-\alpha)Q_1\ \text{for some }\alpha\ge\alpha_0\text{ and distribution }Q_1\text{ on }\mathcal X\big\}.
--   $$
--
--   The worst-case subpopulation risk (2) is the supremum over this set of $\mathbb E_{X\sim Q_0}[\mathbb E[\ell(\theta;(X,Y))\mid X]]$.
--
--   **Formalization Note** $Q_0$ and $Q_1$ are probability measures. The weight $\alpha$ is a nonnegative real with $\alpha\le1$ written out, since $1-\alpha$ must be a mass.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, §1, p.2

import Mathlib

open MeasureTheory
open scoped NNReal

namespace LatentMixDRO

/-- The set of potential minority subpopulations
`P_{α₀,X} = {Q₀ : P_X = α Q₀ + (1 - α) Q₁ for some α ≥ α₀ and distribution Q₁ on 𝒳}`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, §1, p.2.

**Formalization Note.** `α` is an `ℝ≥0`; subtraction there truncates, so `α ≤ 1` is written out
(`1 - α` must be a mass). Both components are probability measures. -/
def uncertaintySet {𝒳 : Type*} [MeasurableSpace 𝒳] (α₀ : ℝ) (PX : Measure 𝒳) : Set (Measure 𝒳) :=
  {Q₀ | IsProbabilityMeasure Q₀ ∧ ∃ α : ℝ≥0, α₀ ≤ (α : ℝ) ∧ α ≤ 1 ∧
    ∃ Q₁ : Measure 𝒳, IsProbabilityMeasure Q₁ ∧ PX = α • Q₀ + (1 - α) • Q₁}

end LatentMixDRO


