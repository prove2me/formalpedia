-- Prove2me | Definitions.Def_BoundedNV_Uniform_UniformDemand
-- name    : BoundedNV_Uniform_UniformDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:59.409105+00:00
-- url     : https://prove2.me/theorems/bfba8415-ca99-42f9-9676-766aefd258bd
-- title:
--   §4.1, pp. 572–573 — uniform demand density on [a, b] and the parameters μ (6), σ (7)
-- statement:
--   This file fixes the uniform-demand instance of §4.1.
--
--   1. **Uniform demand.** For $a < b$, the demand $D \sim U[a, b]$ has density
--   $$f(x) = \frac{1}{b-a}\ \text{ for } x \in [a, b], \qquad f(x) = 0 \text{ otherwise.}$$
--   2. **The parameter $\mu$** of eq. (6), p. 573:
--   $$\mu = b - \frac{c}{p}(b - a).$$
--   3. **The parameter $\sigma$**, the nonnegative square root of eq. (7), p. 573:
--   $$\sigma = \sqrt{\beta\,\frac{b-a}{p}}, \qquad \text{so } \sigma^2 = \beta\,\frac{b-a}{p} \text{ when } \beta, p > 0,\ a < b.$$
--
--   These are the parameters of the truncated normal law that Proposition 1 identifies as the behavioral solution.
--
--   **Formalization Note** The paper assumes $b > a \ge 0$ (p. 572); the theorems carry these hypotheses. `Real.sqrt` of a negative number is $0$, but under the theorems' hypotheses $\beta > 0$, $p > 0$, $a < b$ the radicand is positive, so $\sigma > 0$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 572–573 (PDF 7–8), §4.1, eqs. (6), (7)

import Mathlib

namespace BoundedNV.Uniform

/-- The density of the uniform demand `D ∼ U[a, b]`: `1/(b − a)` on `[a, b]`, `0` elsewhere. -/
noncomputable def unifDensity (a b : ℝ) (x : ℝ) : ℝ :=
  (Set.Icc a b).indicator (fun _ => 1 / (b - a)) x

/-- The parameter `μ = b − (c/p)(b − a)` of eq. (6). -/
noncomputable def unifMu (a b p c : ℝ) : ℝ := b - c / p * (b - a)

/-- The parameter `σ = √(β (b − a)/p)`, so that `σ² = β (b − a)/p` as in eq. (7). -/
noncomputable def unifSigma (a b p β : ℝ) : ℝ := Real.sqrt (β * (b - a) / p)

end BoundedNV.Uniform


