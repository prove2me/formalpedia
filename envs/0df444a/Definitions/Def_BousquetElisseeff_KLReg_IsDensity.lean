-- Prove2me | Definitions.Def_BousquetElisseeff_KLReg_IsDensity
-- name    : BousquetElisseeff_KLReg_IsDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:15.903054+00:00
-- url     : https://prove2.me/theorems/0d7530e3-e009-415d-a086-95dfc07e624b
-- title:
--   Probability densities $\mathcal F$ with respect to the reference measure
-- statement:
--   Let $\Theta$ be a measurable space with a reference measure $\mu$. A function $g : \Theta \to \mathbb R$ is a **density** (an element of the class $\mathcal F$ of §5.2.3) if
--
--   1. $g$ is measurable,
--   2. $g(\theta) \ge 0$ for every $\theta$, and
--   3. $\displaystyle\int_\Theta g\,d\mu = 1$.
--
--   The output of the relative-entropy regularized algorithm is such a density: a posterior distribution over the parameters $\theta$ of the base hypotheses $h_\theta$, used to average their predictions.
--
--   **Formalization Note** The normalization $\int g\,d\mu = 1$ forces $g$ to be integrable (a non-integrable function has Bochner integral $0$ in Lean), so $g\cdot\mu$ is a probability measure. The reference measure is arbitrary; no σ-finiteness is assumed.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, §5.2.3, p. 517 (unnumbered): definition of 𝓕

import Mathlib

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **The class 𝓕 of densities with respect to the reference measure** (§5.2.3).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, §5.2.3, p. 517
(unnumbered): "we assume that Θ is a measurable space where a reference measure is defined. The
output of our algorithm is a mixture of element from Θ, in other words, it is a probability
distribution over Θ. We will thus choose 𝓕 as the set of all such probability distributions
(dominated by the reference measure), defined by their density with respect to the reference
measure."

`IsDensity μ g` says that `g : Θ → ℝ` is a probability density with respect to the reference
measure `μ`: `g` is measurable, nonnegative everywhere, and `∫ g dμ = 1`.

**Formalization Note.** The condition `∫ g dμ = 1` forces `g` to be `μ`-integrable (Mathlib's
Bochner integral of a non-integrable function is `0`), so `μ.withDensity g` is a probability
measure. Densities that agree `μ`-a.e. describe the same distribution; every quantity of the
mission (the averaged loss, the relative entropy) depends only on the a.e. class. The
reference measure `μ` is arbitrary (no σ-finiteness), as on p. 517. -/
def IsDensity {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (g : Θ → ℝ) : Prop :=
  Measurable g ∧ (∀ θ, 0 ≤ g θ) ∧ ∫ θ, g θ ∂μ = 1

end BousquetElisseeff.KLReg


