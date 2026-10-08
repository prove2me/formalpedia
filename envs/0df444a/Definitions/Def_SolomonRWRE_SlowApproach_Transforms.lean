-- Prove2me | Definitions.Def_SolomonRWRE_SlowApproach_Transforms
-- name    : SolomonRWRE_SlowApproach_Transforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:46.8489+00:00
-- url     : https://prove2.me/theorems/395c07ed-f243-4b95-820b-2aba64e9d95c
-- title:
--   §2 — transform parameters, comparison series, and the limiting law
-- statement:
--   The characteristic-root formulas (2.3)–(2.4) define $\lambda_1(u)$, $\lambda_2(u)$, $a(u)$, $b(u)$, $c(u)$, and $\beta(u)=\theta^{-1}\lambda_1(u)$. They define the exact series for the mirror-to-mirror passage-time Laplace transform and the comparison series $\psi(u)$ of (2.6). The bilateral series in (2.12) specifies a family $F_\varepsilon$ of probability laws on $[0,\infty)$ by
--   $$
--   \int e^{-ux}\,dF_\varepsilon(x)=\exp\left[-Ku\sum_{j\in\mathbb Z}\frac{(\gamma\theta)^{j-\varepsilon}}{1+\nu u\theta^{j-\varepsilon}}\right],\qquad u>0.
--   $$
--   This law is the target of the subsequential limits. The exact characteristic-root formulas, rather than their small-$u$ expansions, are used throughout.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 12–14, displays (2.3)–(2.4), (2.12)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Model

namespace SolomonRWRE.SlowApproach

/-- Solomon, §2, p. 12, displays (2.3)–(2.4). -/
noncomputable def lambdaOne (θ u : ℝ) : ℝ :=
  Real.exp u / 2 * (θ + 1 + Real.sqrt ((θ + 1) ^ 2 - 4 * θ * Real.exp (-2 * u)))
noncomputable def lambdaTwo (θ u : ℝ) : ℝ :=
  Real.exp u / 2 * (θ + 1 - Real.sqrt ((θ + 1) ^ 2 - 4 * θ * Real.exp (-2 * u)))
noncomputable def aU (θ u : ℝ) : ℝ := lambdaOne θ u - Real.exp u
noncomputable def bU (θ u : ℝ) : ℝ := Real.exp u - lambdaTwo θ u
noncomputable def cU (θ u : ℝ) : ℝ := lambdaOne θ u - lambdaTwo θ u
noncomputable def betaU (θ u : ℝ) : ℝ := θ⁻¹ * lambdaOne θ u

/-- Solomon, §2, p. 12, right side of Lemma (2.5). -/
noncomputable def phiSeries (γ θ u : ℝ) : ℝ :=
  (1 - γ) / γ * ∑' j : ℕ,
    cU θ u * (γ * betaU θ u) ^ (j + 1) /
      (aU θ u + bU θ u * (θ * (betaU θ u) ^ 2) ^ (j + 1))

/-- Solomon, §2, p. 12, comparison transform before Lemma (2.6). -/
noncomputable def psi (γ θ u : ℝ) : ℝ :=
  (1 - γ) / γ * ∑' j : ℕ,
    γ ^ (j + 1) / (1 + nu θ * u * θ ^ (j + 1))

/-- Solomon, §2, pp. 13–14, the two-sided series in (2.9) and (2.12). -/
noncomputable def laplaceSeries (γ θ ε u : ℝ) : ℝ :=
  ∑' j : ℤ, (γ * θ) ^ ((j : ℝ) - ε) /
    (1 + nu θ * u * θ ^ ((j : ℝ) - ε))

/-- Solomon, Lemma (2.10)(ii), p. 14, and Theorem (2.20)(ii), p. 19.
The family is a probability law on the nonnegative reals with Laplace transform (2.12). -/
def IsLimitLaw (F : ℝ → MeasureTheory.Measure ℝ) (γ θ : ℝ) : Prop :=
  (∀ ε, MeasureTheory.IsProbabilityMeasure (F ε)) ∧
  (∀ ε, F ε (Set.Iio 0) = 0) ∧
  (∀ ε u, 0 < u →
    (∫ x, Real.exp (-u * x) ∂(F ε)) =
      Real.exp (-K γ θ * u * laplaceSeries γ θ ε u))

end SolomonRWRE.SlowApproach


