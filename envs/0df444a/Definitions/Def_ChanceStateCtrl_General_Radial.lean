-- Prove2me | Definitions.Def_ChanceStateCtrl_General_Radial
-- name    : ChanceStateCtrl_General_Radial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:52.139656+00:00
-- url     : https://prove2.me/theorems/87e87606-7110-4158-a40a-987245a79662
-- title:
--   (13), (17), (19), pp. 5–7 — chi law μ_η, uniform sphere law μ_ζ, radial probability function e, radius ρ, Aumann integral
-- statement:
--   This module defines the objects of the spherical-radial decomposition used in §2.1 of Geiersbach and Henrion.
--
--   Let $\mathbb S^{m-1}=\{v\in\mathbb R^m\mid\|v\|_2=1\}$, let $\Sigma^{1/2}$ be the root of the covariance matrix fixed in the Setting module, and let $g:U\times\mathbb R^m\to\mathbb R$.
--
--   1. **Chi distribution** $\mu_\eta$ with $m$ degrees of freedom: the law on $\mathbb R$ with density $\chi(t)=K\,t^{m-1}e^{-t^2/2}$ for $t\ge0$ and $0$ for $t<0$, where $K=\big(\int_0^\infty t^{m-1}e^{-t^2/2}\,dt\big)^{-1}$; its distribution function is $F_\eta(t)=\mu_\eta((-\infty,t])$.
--   2. **Uniform distribution** $\mu_\zeta$ on $\mathbb S^{m-1}$: the surface measure induced by Lebesgue measure on $\mathbb R^m$, normalized to total mass one.
--   3. **Radial probability function** (13):
--   $$
--   e(u,v)=\mu_\eta\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\},\qquad u\in U,\ v\in\mathbb S^{m-1}.
--   $$
--   4. **Radius function** of (17): $\rho(u,v)=\sup\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}\in[0,\infty]$.
--   5. **Aumann integral** of a set-valued map $\Phi:\mathbb S^{m-1}\rightrightarrows U^*$ with respect to a measure $\mu$: the set of $x^*\in U^*$ for which there is a selection $\hat x^*_v\in\Phi(v)$ (for $\mu$-a.e. $v$) such that each $v\mapsto\langle\hat x^*_v,h\rangle$ is $\mu$-integrable and
--   $$
--   x^*(h)=\int\hat x^*_v(h)\,d\mu(v)\qquad\forall h\in U .
--   $$
--
--   With these objects the paper writes $\varphi$ as $\int_{\mathbb S^{m-1}}e(u,v)\,d\mu_\zeta(v)$ in (14) and estimates or computes $\partial^C\varphi$ as the Aumann integral of the partial Clarke subdifferentials $\partial^C_ue(\bar u,v)$ in (15) and Theorem 2.4.
--
--   **Formalization Note** $\mu_\zeta$ is Mathlib's `Measure.toSphere` of Lebesgue measure divided by its total mass. The paper defines $\rho$ only on $\mathcal N(\bar u)\times\mathbb S^{m-1}$, where $g(u,0)<0$ makes the set nonempty; the definition above is the supremum everywhere, valued in $[0,\infty]$ (`ENNReal`), and agrees with the paper's $\rho$ wherever the paper defines it. The paper requires the selection of the Aumann integral to be measurable (p. 6); here this is the weak-$*$ (scalar) measurability carried by the integrability of every $v\mapsto\langle\hat x^*_v,h\rangle$, which is the form in which Clarke's theorem on integral functionals uses it.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 5–7: (13), (14) (μ_ζ), p. 6 (Aumann integral, (17), (19), F_η)

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder

namespace ChanceStateCtrl.General

/-- Normalizing constant `K` of the chi density with `m` degrees of freedom. -/
noncomputable def chiConst (m : ℕ) : ℝ :=
  (∫ t in Set.Ioi (0 : ℝ), t ^ (m - 1) * Real.exp (-t ^ 2 / 2))⁻¹

/-- The chi density `χ(t) = K t^{m-1} e^{-t²/2}` for `t ≥ 0`, and `0` for `t < 0`. -/
noncomputable def chiDensity (m : ℕ) (t : ℝ) : ℝ :=
  if 0 ≤ t then chiConst m * t ^ (m - 1) * Real.exp (-t ^ 2 / 2) else 0

/-- The (one-dimensional) chi distribution `μ_η` with `m` degrees of freedom. -/
noncomputable def chiLaw (m : ℕ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (chiDensity m t))

/-- The cumulative distribution function `F_η(t) = μ_η((-∞, t])` of the chi distribution. -/
noncomputable def chiCDF (m : ℕ) (t : ℝ) : ℝ :=
  (chiLaw m (Set.Iic t)).toReal

/-- The uniform distribution `μ_ζ` on the unit sphere `S^{m-1}` of `ℝᵐ`: the surface measure
induced by Lebesgue measure, normalized to total mass one. -/
noncomputable def sphereLaw (m : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere

/-- The radial probability function (13): `e(u, v) = μ_η{r ≥ 0 | g(u, r Σ^{1/2} v) ≤ 0}`. -/
noncomputable def radialProb {U : Type*} {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (u : U)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : ℝ :=
  (chiLaw m {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0}).toReal

/-- The radius function of (17), with values in `[0, ∞]`:
`ρ(u, v) = sup {r ≥ 0 | g(u, r Σ^{1/2} v) ≤ 0}`. -/
noncomputable def radius {U : Type*} {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (u : U)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : ENNReal :=
  ⨆ r ∈ {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0},
    ENNReal.ofReal r

/-- The Aumann integral `∫ Φ(v) dμ(v)` of a set-valued map `Φ : V ⇉ U*`: the set of `x* ∈ U*` for
which there is a selection `s(v) ∈ Φ(v)` (for `μ`-a.e. `v`) such that every `v ↦ ⟨s(v), h⟩` is
`μ`-integrable and `⟨x*, h⟩ = ∫ ⟨s(v), h⟩ dμ(v)` for all `h ∈ U`. -/
def aumann {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [MeasurableSpace V]
    (μ : Measure V) (Φ : V → Set (StrongDual ℝ U)) : Set (StrongDual ℝ U) :=
  {x | ∃ s : V → StrongDual ℝ U, (∀ᵐ v ∂μ, s v ∈ Φ v) ∧
    (∀ h : U, Integrable (fun v => s v h) μ) ∧ ∀ h : U, x h = ∫ v, s v h ∂μ}

end ChanceStateCtrl.General


