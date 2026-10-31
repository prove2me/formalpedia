-- Prove2me | Definitions.Def_ReviewProvision_truncatedMoments
-- name    : ReviewProvision_truncatedMoments
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:37.783123+00:00
-- url     : https://prove2.me/theorems/65ee3415-a7ce-4862-936f-01df957c6075
-- title:
--   The functions $\phi$, $g$, $\tilde g$ and $\Pi_2$
-- statement:
--   Let $\phi$ be the standard normal density. For $\sigma>0$,
--
--   $$
--   g(\sigma)=\int_{-1/\sigma}^{+\infty}z\Bigl(z+\frac1\sigma\Bigr)\phi(z)\,dz,\qquad
--   \tilde g(\sigma)=\int_{-1/\sigma}^{+\infty}z(z\sigma+1)\phi(z)\,dz .
--   $$
--
--   For $\sigma\ge0$ and $Z\sim N(0,1)$,
--
--   $$
--   \Pi_2(\sigma)=\mathbb E\bigl[((1+\sigma Z)^+)^2\bigr].
--   $$
--
--   These are the functions through which the variance of the customer evaluation enters the profit and its first-order conditions.
--
--   **Formalization Note** $\Pi_2$ is defined by the expectation, so it is meaningful at $\sigma=0$, where the integral of (6) has no lower limit (in Lean $-1/0=0$ would give half the right value).
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), (6), p.15; Lemma 8, p.36

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- The standard normal density `φ(z) = (1/√(2π)) exp{−z²/2}`, (6), p.15 (PDF 15). -/
noncomputable def phi (z : ℝ) : ℝ := (1 / √(2 * Real.pi)) * Real.exp (-z ^ 2 / 2)

/-- `g(σ) = ∫_{−1/σ}^{+∞} z(z + 1/σ) φ(z) dz`, Lemma 8, p.36 (PDF 36). Meaningful for `σ > 0`. -/
noncomputable def g (σ : ℝ) : ℝ := ∫ z in Set.Ioi (-1 / σ), z * (z + 1 / σ) * phi z

/-- `g̃(σ) = ∫_{−1/σ}^{+∞} z(zσ + 1) φ(z) dz`, Lemma 8, p.36 (PDF 36). Meaningful for `σ > 0`. -/
noncomputable def gTilde (σ : ℝ) : ℝ := ∫ z in Set.Ioi (-1 / σ), z * (z * σ + 1) * phi z

/-- The second-period moment `Π_2(σ) = E[((1 + σ Z)⁺)²]` for `Z ∼ N(0, 1)`, §3.4 and (6), p.15 (PDF 15).

**Formalization Note.** Defined by the expectation, so it has no `1/σ` and is meaningful at `σ = 0`,
where the lower limit of the integral of (6) is undefined (in Lean `−1/0 = 0`, which would give half
the right value). The integral form is the theorem `eq_6`. -/
noncomputable def Pi2 (σ : ℝ) : ℝ := ∫ z, (max (1 + σ * z) 0) ^ 2 ∂(gaussianReal 0 1)

end ReviewProvision


