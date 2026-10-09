-- Prove2me | Definitions.Def_DistCov_Converse_Setting
-- name    : DistCov_Converse_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:35.721976+00:00
-- url     : https://prove2.me/theorems/03ad08d0-74ac-4841-9887-99a80be69635
-- title:
--   pp. 3–4, 9, 11, 17 — finite first moment, a_µ, D(µ), D(µ₁ − µ₂), d_µ, dcov(θ), product measures, negative and strong negative type, the two-point law and the Dirac mixture
-- statement:
--   Let $(\mathcal X,d)$ and $(\mathcal Y,d)$ be separable metric spaces with their Borel $\sigma$-fields. This file fixes the objects of §2 and §3 of Lyons' paper that Proposition 3.15 is about.
--
--   1. **Finite first moment.** A finite (positive) Borel measure $\mu$ on $\mathcal X$ has a *finite first moment* if $\int d(o,x)\,d\mu(x)<\infty$ for some $o\in\mathcal X$.
--   2. **Mean distance and energy.** $a_\mu(x):=\int d(x,x')\,d\mu(x')$, and for two measures the energy $E(\mu_1,\mu_2):=\iint d(x,x')\,d\mu_1(x)\,d\mu_2(x')$. Then $D(\mu):=E(\mu,\mu)=\int d(x,x')\,d\mu^2(x,x')$.
--   3. **Energy of a difference.** For finite measures $\mu_1,\mu_2$,
--   $$D(\mu_1-\mu_2):=E(\mu_1,\mu_1)-2E(\mu_1,\mu_2)+E(\mu_2,\mu_2),$$
--   the bilinear expansion of $\int d\,d(\mu_1-\mu_2)^2$.
--   4. **Doubly centred distance.** $d_\mu(x,x'):=d(x,x')-a_\mu(x)-a_\mu(x')+D(\mu)$.
--   5. **Distance covariance.** For a probability measure $\theta$ on $\mathcal X\times\mathcal Y$ with marginals $\mu$ on $\mathcal X$ and $\nu$ on $\mathcal Y$,
--   $$\operatorname{dcov}(\theta):=\int d_\mu(x,x')\,d_\nu(y,y')\,d\theta^2\big((x,y),(x',y')\big).$$
--   6. **Product measure.** $\theta$ *is a product measure* if $\theta=\mu\times\nu$ for its own marginals $\mu,\nu$.
--   7. **Negative type (3.1).** $\mathcal X$ has *negative type* if for all $n$, all $x_1,\dots,x_n\in\mathcal X$ and all $\alpha_1,\dots,\alpha_n\in\mathbb R$ with $\sum_i\alpha_i=0$, $\sum_{i,j\le n}\alpha_i\alpha_j\,d(x_i,x_j)\le 0$.
--   8. **Strong negative type (p. 11).** $\mathcal X$ has *strong negative type* if it has negative type and, for Borel probability measures $\mu_1,\mu_2$ with finite first moments, $D(\mu_1-\mu_2)=0$ only when $\mu_1=\mu_2$.
--   9. **The constructions of the proof of Proposition 3.15 (p. 17).** For $\mu_1,\mu_2$ on $\mathcal X$ and $y_1,y_2\in\mathcal Y$, the two-point law $\theta:=\big(\mu_1\times\delta(y_1)+\mu_2\times\delta(y_2)\big)/2$; and for $\gamma\in[0,1]$, $x\in\mathcal X$, the mixture $\tau:=\gamma\mu+(1-\gamma)\delta(x)$, where $\delta(y)$ is the point mass at $y$.
--
--   These are the objects in which Proposition 3.15 and the steps of its proof are stated.
--
--   **Formalization Note.** Measures are Mathlib `Measure`s; a probability measure is one with the `IsProbabilityMeasure` instance, and marginals are push-forwards under the projections. Mathlib's Bochner integral does not integrate against signed measures, so $D(\mu_1-\mu_2)$ is the energy expansion above; the two cross terms agree by symmetry of $d$ and Fubini. A Bochner integral of a non-integrable function is $0$ in Lean, so every theorem using $a_\mu$, $D$, $d_\mu$ or $\operatorname{dcov}$ assumes (or concludes) the finite first moments that make these integrals honest. The case $n=0$ of (3.1), which the paper excludes with $n\ge1$, is harmless: both sides are $0$. Weights of measures are extended nonnegative reals; $\gamma$ and $1-\gamma$ enter through `ENNReal.ofReal`, which is faithful only for $\gamma\in[0,1]$, so every theorem using the mixture assumes $\gamma\in(0,1]$. Separability is not needed to state the definitions; it is a hypothesis of every theorem (Errata (i)).
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), pp. 3–4 (§2), p. 9 (3.1), p. 11 (3.3) and strong negative type, p. 17 (proof of Proposition 3.15); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Converse

open MeasureTheory
open scoped ENNReal

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y]

/-- θ := (µ₁ × δ(y₁) + µ₂ × δ(y₂))/2 (p. 17). -/
noncomputable def twoPointLaw (μ₁ μ₂ : Measure X) (y₁ y₂ : Y) : Measure (X × Y) :=
  (2 : ℝ≥0∞)⁻¹ • (μ₁.prod (Measure.dirac y₁) + μ₂.prod (Measure.dirac y₂))

/-- τ := γµ + (1 − γ)δ(x) (p. 17), for γ ∈ [0, 1]. -/
noncomputable def mixDirac (γ : ℝ) (μ : Measure X) (x : X) : Measure X :=
  ENNReal.ofReal γ • μ + ENNReal.ofReal (1 - γ) • Measure.dirac x

end DistCov.Converse


