-- Prove2me | Definitions.Def_TentNoise_reflHeatDensity
-- name    : TentNoise_reflHeatDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:03.970206+00:00
-- url     : https://prove2.me/theorems/0ee88b26-4891-474d-953b-ccf0527f56e8
-- title:
--   The reflected heat kernel density $h_\sigma(a,y)$
-- statement:
--   For $\sigma>0$ let $q_\sigma$ be the density of $\mathcal N(0,\sigma^2)$. The **density of the reflected Gaussian kernel** with respect to $\mu$ is, by the method of images,
--
--   $$
--   h_\sigma(a,y)=\sum_{j\in\mathbb Z}\Bigl[q_\sigma(y-a+2j)+q_\sigma(y+a+2j)\Bigr],\qquad a,y\in[0,1].
--   $$
--
--   It is the Neumann heat kernel on $[0,1]$ and coincides with the spectral series $h_\sigma(a,y)=1+2\sum_{n\ge1}e^{-\pi^2n^2\sigma^2/2}\cos(n\pi a)\cos(n\pi y)$ of eq. (29).
--
--   Its supremum $M_\sigma$ controls how much the noised fitted chain can concentrate.
--
--   **Formalization Note** Valued in $[0,\infty]$ (Mathlib's `gaussianPDF`), so the series always has a value. It is meaningful for $\sigma>0$; at $\sigma=0$ the Gaussian density is $0$ in Mathlib and $H_0$ has no density. Every theorem using it assumes $\sigma>0$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), proof of Lemma B.5, p.28 (image sum); Lemma A.5, eq. (29), p.18 (spectral form)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TentNoise

/-- The density `h_σ(a, y)` of the reflected Gaussian kernel with respect to `µ`, by the method of
images: `h_σ(a, y) = ∑_{j∈ℤ} [q_σ(y − a + 2j) + q_σ(y + a + 2j)]`, where `q_σ` is the density of
`N(0, σ²)` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), proof of Lemma B.5, p.28; the same function as the spectral series (29), p.18).

**Formalization Note** Valued in `[0, ∞]` (Mathlib's `gaussianPDF`), so the series always has a
value and no summability side condition arises. It is meaningful for `σ > 0` (at `σ = 0` the Gaussian
density is identically `0`, and the kernel `H₀` has no density); every theorem using it assumes
`σ > 0`, as Lemma A.5 does. -/
noncomputable def reflHeatDensity (σ a y : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, (gaussianPDF 0 (σ ^ 2).toNNReal (y - a + 2 * j) +
    gaussianPDF 0 (σ ^ 2).toNNReal (y + a + 2 * j))

end TentNoise


