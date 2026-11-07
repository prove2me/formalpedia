-- Prove2me | Definitions.Def_GaussMixHH_RadialTransform
-- name    : GaussMixHH_RadialTransform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:05.799758+00:00
-- url     : https://prove2.me/theorems/903c8a19-9434-4c1d-81a2-038b1fd7ff72
-- title:
--   The transform $G_\nu$, the Gaussian factor $(1-2i\theta)^{-n/2}$, $\Phi_\rho$, $\mathrm{Diff}_\nu$ and the observation disk $B$
-- statement:
--   For a finite measure $\mu$ on radii and $s\in\mathbb C$,
--
--   $$G_\mu(s)=\int e^{s r^2}\,d\mu(r),$$
--
--   which is well defined for $\operatorname{Re}s\le0$; for a signed measure $\nu=\mu_1-\mu_2$, $G_\nu=G_{\mu_1}-G_{\mu_2}$. Put
--
--   $$w(\theta)=\frac{i\theta}{1-2i\theta},\qquad \Phi_\rho(\theta)=(1-2i\theta)^{-n/2}\,G_\rho(w(\theta)),\qquad \mathrm{Diff}_\nu(\theta)=(1-2i\theta)^{-n/2}\,G_\nu(w(\theta)),$$
--
--   for $\theta\in\mathbb R$, a radial probability distribution $\rho$ and $n\in\mathbb N$. $\Phi_\rho$ is the right side of the radial identity (6). The **observation disk** is
--
--   $$B=\{s\in\mathbb C:\ |s+\tfrac14|<\tfrac14\},$$
--
--   the disk whose boundary circle is traced by $w(\theta)$.
--
--   These objects carry the paper's complex-analytic argument: an observable difference of characteristic functions is the value of $(1+2s)^{n/2}G_\nu(s)$ on $\partial B$.
--
--   **Formalization Note** $(1-2i\theta)^{-n/2}$ is `Complex.cpow` with exponent $-n/2$, the principal branch ($\operatorname{Re}(1-2i\theta)=1>0$). $G_\mu$ is a Bochner integral; for $\operatorname{Re}s\le0$ and finite $\mu$ the integrand has modulus at most $1$, so no junk value arises where the paper uses it. A signed measure is passed as a pair of finite measures.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), §2.1, p.9 (PDF p.11); §4.1, pp.18–19 (PDF pp.20–21), eq. (6)

import Mathlib

open MeasureTheory Complex

namespace GaussMixHH

/-!
# The exponential transform `G_ν`, the Gaussian factor and the observation disk

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), §2.1, p.9, and §4.1, pp.18–19
(PDF pp.11, 20–21): Lemma 12, eq. (6), the functions `G_ν`, `Diff_ν`, `Ψ` and the disk `B`.

For a finite measure `ν` on `[0, ∞)` (a law of radii `r`), `G_ν(s) = ∫ e^{s r²} dν(r)` for
`Re s ≤ 0`; `w(θ) = iθ/(1 − 2iθ)`; and for a radial probability distribution `ρ`,
`Φ_ρ(θ) = (1 − 2iθ)^{−n/2} G_ρ(w(θ))`, the right side of (6). For two finite measures
`μ₁, μ₂`, `Diff_ν(θ) = (1 − 2iθ)^{−n/2} G_ν(w(θ))` with `ν = μ₁ − μ₂`.

**Formalization Note.**
* `(1 − 2iθ)^{−n/2}` is `Complex.cpow` with exponent `−n/2`, the principal branch
  (`Re(1 − 2iθ) = 1 > 0`), as the paper intends (p.19).
* A signed measure `ν` is passed as a pair `μ₁, μ₂` of finite measures with `ν = μ₁ − μ₂`, and
  `G_ν = G_{μ₁} − G_{μ₂}`; by the Jordan decomposition every finite real signed measure arises.
* `G_μ(s)` is a Bochner integral. For `Re s ≤ 0` and a finite measure the integrand has modulus
  at most `1`, so it is integrable and no junk value arises on the domain where the paper uses it.
-/

/-- `w(θ) = iθ/(1 − 2iθ)`. -/
noncomputable def wfun (θ : ℝ) : ℂ := I * θ / (1 - 2 * I * θ)

/-- The Gaussian factor `(1 − 2iθ)^{−n/2}` (principal branch). -/
noncomputable def gaussFactor (n : ℕ) (θ : ℝ) : ℂ := (1 - 2 * I * θ) ^ (-(n : ℂ) / 2)

/-- `G_μ(s) = ∫ e^{s r²} dμ(r)` for a measure `μ` on radii. -/
noncomputable def Gfun (μ : Measure ℝ) (s : ℂ) : ℂ := ∫ r, cexp (s * (r : ℂ) ^ 2) ∂μ

/-- `Φ_ρ(θ) = (1 − 2iθ)^{−n/2} ∫ e^{w(θ) r²} dρ(r)`, the right side of (6). -/
noncomputable def PhiRad (n : ℕ) (ρ : Measure ℝ) (θ : ℝ) : ℂ :=
  gaussFactor n θ * Gfun ρ (wfun θ)

/-- `Diff_ν(θ) = (1 − 2iθ)^{−n/2} G_ν(w(θ))` for `ν = μ₁ − μ₂`. -/
noncomputable def DiffNu (n : ℕ) (μ₁ μ₂ : Measure ℝ) (θ : ℝ) : ℂ :=
  gaussFactor n θ * (Gfun μ₁ (wfun θ) - Gfun μ₂ (wfun θ))

/-- The observation disk `B = {s ∈ ℂ : |s + 1/4| < 1/4}`. -/
def obsDisk : Set ℂ := Metric.ball (-1 / 4 : ℂ) (1 / 4)

end GaussMixHH


