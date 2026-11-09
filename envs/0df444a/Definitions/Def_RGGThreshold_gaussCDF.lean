-- Prove2me | Definitions.Def_RGGThreshold_gaussCDF
-- name    : RGGThreshold_gaussCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:28.224484+00:00
-- url     : https://prove2.me/theorems/e4a9661e-ab7f-460c-9535-279c7fa8dc55
-- title:
--   Standard Gaussian $\Phi$, $\phi$, $\lambda=\phi/\Phi$, the quantile $z_p$ and $a=\phi(z_p)$
-- statement:
--   Let $\phi(t)=e^{-t^2/2}/\sqrt{2\pi}$ be the density of the standard Gaussian $N(0,1)$ and $\Phi(t)=\int_{-\infty}^t\phi(x)\,dx$ its distribution function. Define
--
--   $$
--   \lambda(t)=\frac{\phi(t)}{\Phi(t)},\qquad z_p=\Phi^{-1}(1-p),\qquad a=\phi(z_p),
--   $$
--
--   so that $z_p$ is the unique real number with $\mathbb P[N(0,1)\ge z_p]=p$ for $p\in(0,1)$. These quantities enter every estimate of the paper: the edge probabilities of the random geometric graph are compared with Gaussian tails at $z_p$, and $a$ is the Gaussian density at that point.
--
--   **Formalization Note** $\Phi$ is Mathlib's distribution function of `gaussianReal 0 1` and $\phi$ is `gaussianPDFReal 0 1`. The quantile is written as $z_p=\inf\{z:1-p\le\Phi(z)\}$; for $p\in(0,1)$ this infimum satisfies $\Phi(z_p)=1-p$ and $\mathbb P[N(0,1)\ge z_p]=p$ (both proved in the mission's sanity file). For $p\notin(0,1)$ the value is a placeholder that no statement uses.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), §2.1, p.4 (PDF p.6); §4.2, pp.12–13 (PDF pp.14–15)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RGGThreshold

/-- The standard Gaussian distribution function `Φ(t) = ∫_{-∞}^t ϕ(x) dx` (Hunter–Milojević–Sudakov,
*Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256
1a398ef9…, §4.2, p.12 (PDF p.14); also §2.1, p.4).

**Formalization Note** `Φ` is Mathlib's cumulative distribution function of `gaussianReal 0 1`, the
law `N(0, 1)`. -/
noncomputable def gaussCDF (t : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

/-- The standard Gaussian density `ϕ(t) = e^{-t²/2}/√(2π)` (arXiv:2607.22480, held version, §4.2,
p.12 (PDF p.14)). -/
noncomputable def gaussPDF (t : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 t

/-- The ratio `λ(t) = ϕ(t)/Φ(t)` (arXiv:2607.22480, held version, §4.2, p.12 (PDF p.14)). Since
`Φ(t) > 0` for every real `t`, the division never meets a zero denominator. -/
noncomputable def millsLam (t : ℝ) : ℝ :=
  gaussPDF t / gaussCDF t

/-- The Gaussian quantile `z_p = Φ^{-1}(1 - p)`, the unique real number with `P[N(0,1) ≥ z_p] = p`
(arXiv:2607.22480, held version, §2.1, p.4 (PDF p.6); §4.2, p.13 (PDF p.15)).

**Formalization Note** It is written as `inf {z | 1 - p ≤ Φ(z)}`. For `p ∈ (0, 1)` this set is a
nonempty closed half-line bounded below, and its infimum is the unique `z` with `Φ(z) = 1 - p`
(proved in the mission's sanity file). Outside `(0, 1)` the value is a junk value that no
statement of the mission uses. -/
noncomputable def zp (p : ℝ) : ℝ :=
  sInf {z : ℝ | 1 - p ≤ gaussCDF z}

/-- The constant `a = ϕ(z_p) = e^{-z_p²/2}/√(2π)` (arXiv:2607.22480, held version, §2.1, p.4
(PDF p.6)). -/
noncomputable def aCoef (p : ℝ) : ℝ :=
  gaussPDF (zp p)

end RGGThreshold


