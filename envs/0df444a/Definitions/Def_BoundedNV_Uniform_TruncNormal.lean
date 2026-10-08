-- Prove2me | Definitions.Def_BoundedNV_Uniform_TruncNormal
-- name    : BoundedNV_Uniform_TruncNormal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:08.081763+00:00
-- url     : https://prove2.me/theorems/df66c534-4b1c-463f-be51-aec417c3d6bc
-- title:
--   Proof of Proposition 1, eq. (37), p. 586 — the density of a normal law truncated to [a, b]
-- statement:
--   Let $a < b$, $\mu \in \mathbb R$ and $\sigma > 0$. The **truncated normal density** over $[a, b]$ with parameters $\mu$ and $\sigma^2$ is
--   $$\zeta(x) = \frac{e^{-(x-\mu)^2/2\sigma^2}}{\int_a^b e^{-(v-\mu)^2/2\sigma^2}\,dv}, \qquad x \in [a, b],$$
--   and $\zeta(x) = 0$ for $x \notin [a, b]$ (eq. (37), p. 586).
--
--   It is the law of a $N(\mu, \sigma^2)$ variable conditioned on lying in $[a, b]$. Proposition 1 identifies the behavioral solution of the newsvendor with uniform demand as such a law.
--
--   **Formalization Note** $\mu$ and $\sigma^2$ are the parameters of the normal law *before* truncation; they are not the mean and variance of $\zeta$ unless the truncation is symmetric about $\mu$ (and even then the variance differs). The density depends on $\sigma$ only through $\sigma^2$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 586 (PDF 21), Proof of Proposition 1, eq. (37)

import Mathlib

namespace BoundedNV.Uniform

/-- The density (37) of the normal law with parameters `μ` and `σ²` truncated to `[a, b]`:
`ζ(x) = e^{-(x-μ)²/2σ²} / ∫_a^b e^{-(v-μ)²/2σ²} dv` on `[a, b]`, and `0` off `[a, b]`.
`μ` and `σ²` are the parameters of the normal law before truncation. -/
noncomputable def truncNormalDensity (a b μ σ : ℝ) (x : ℝ) : ℝ :=
  (Set.Icc a b).indicator
    (fun x => Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2)) /
      ∫ v in Set.Icc a b, Real.exp (-(v - μ) ^ 2 / (2 * σ ^ 2))) x

end BoundedNV.Uniform


