-- Prove2me | Definitions.Def_PrivBayesTest_bayesRisk
-- name    : PrivBayesTest_bayesRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:50.480761+00:00
-- url     : https://prove2.me/theorems/18c17df3-8f80-40fe-a272-f27223f5c097
-- title:
--   Bayes risk $P_e^{(n)}=\pi_0\alpha_n+\pi_1\beta_n$ of a test
-- statement:
--   A **test** on $n$ samples is a Markov kernel $T$ from $\mathcal X^n$ to $\{\text{"}P\text{"},\text{"}Q\text{"}\}$ (encoded as Booleans, $\mathrm{true}=$ "$P$"). Its false positive rate is $\alpha_n=\Pr(\text{output is "}Q\text{"}\mid X\sim P^n)$ and its false negative rate is $\beta_n=\Pr(\text{output is "}P\text{"}\mid X\sim Q^n)$. For a prior $(\pi_0,\pi_1)$ on $\{P,Q\}$ the **Bayes risk** is
--
--   $$
--   P_e^{(n)} \;=\; \pi_0\,\alpha_n + \pi_1\,\beta_n .
--   $$
--
--   **Formalization Note** The risk is an extended nonnegative real. A test $T\circ M$ of the paper (a mechanism $M$ followed by a post-processing $T$) is itself a Markov kernel to the two outputs, and every such kernel is of this form, so tests are represented by these kernels. The paper's standing assumption $\pi_0,\pi_1>0$ (p.1) is a hypothesis of the theorems that use this definition.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), §1.1, p.1

import Mathlib
import Definitions.Def_PrivBayesTest_outLaw

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- The **Bayes risk** `P_e^{(n)} = π₀ αₙ + π₁ βₙ` of a test on `n` samples (Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), §1.1, p.1).

A test is a Markov kernel `κ` from `Xⁿ` to `Bool`, with `true` meaning the output "`P`" and
`false` the output "`Q`". Its false positive rate is `αₙ = Pr(output "Q" | X ∼ Pⁿ)`, its false
negative rate is `βₙ = Pr(output "P" | X ∼ Qⁿ)`, and `(π₀, π₁)` is the prior on `{P, Q}`.

**Formalization Note** The risk is an extended nonnegative real (`ENNReal.ofReal π_i` times the
probabilities). Every test `T ∘ M` of the paper (an ε-DP mechanism `M` followed by a post-processing
`T : Y → {"P","Q"}`) is such a kernel, and every such kernel is `T ∘ M` with `M` the kernel itself and
`T` the identity. The prior's standing assumption `π₀, π₁ > 0` (p.1) is a hypothesis of the theorems
that use this definition. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] {n : ℕ} (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (π₀ π₁ : ℝ) (κ : Kernel (Fin n → X) Bool) :
    ENNReal :=
  ENNReal.ofReal π₀ * outLaw κ P {false} + ENNReal.ofReal π₁ * outLaw κ Q {true}

end PrivBayesTest


