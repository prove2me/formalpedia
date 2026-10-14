-- Prove2me | Definitions.Def_ChanceStateCtrl_PDE_Setting
-- name    : ChanceStateCtrl_PDE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:02.290277+00:00
-- url     : https://prove2.me/theorems/01bd866a-68c7-4bc4-a9ac-2e61b80370fe
-- title:
--   §1.1, §2.1, pp. 3–6, 11 — global minimality, Clarke derivative and subdifferential on L², probability function, χ, μ_η, μ_ζ, e, ρ, (12), Aumann integral
-- statement:
--   General objects of the paper's §2.1, for a control space $U$ (later $U=L^2(D)$) and a random vector in $\mathbb R^m$.
--
--   1. **Solution.** $u^*$ is a solution of $\min\{F(u)\mid u\in\mathcal U\}$ if $u^*\in\mathcal U$ and $F(u^*)\le F(u)$ for all $u\in\mathcal U$ (global minimality).
--   2. **Clarke calculus** (p. 3). For $f:U\to\mathbb R$, the Clarke directional derivative is
--   $$f^\circ(u;h)=\limsup_{u'\to u,\ t\downarrow0}\frac{f(u'+th)-f(u')}{t},$$
--   $f$ is locally Lipschitzian around $u$ if it is Lipschitz on some neighbourhood of $u$, and on a real Hilbert space $H$ (dual identified with $H$) the Clarke subdifferential is $\partial^Cf(u)=\{y\in H\mid \langle y,h\rangle\le f^\circ(u;h)\ \forall h\in H\}$.
--   3. **Probability function** (9): $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ for $g:U\times\mathbb R^m\to\mathbb R$.
--   4. **Root of $\Sigma$**: $\Sigma^{1/2}$, the positive semidefinite square root of the covariance matrix, as a linear map of $\mathbb R^m$.
--   5. **Chi law**: $\chi(t)=Kt^{m-1}e^{-t^2/2}$ for $t\ge0$ (and $0$ for $t<0$), $K=(\int_0^\infty t^{m-1}e^{-t^2/2}\,dt)^{-1}$, and $\mu_\eta$ the measure on $\mathbb R$ with density $\chi$.
--   6. **Uniform sphere law** $\mu_\zeta$: the surface measure on $\mathbb S^{m-1}=\{v\in\mathbb R^m\mid\|v\|_2=1\}$ normalized to total mass $1$.
--   7. **Radial probability function** (13) and **radius function** (17):
--   $$e(u,v)=\mu_\eta\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\},\qquad \rho(u,v)=\sup\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}\in[0,\infty].$$
--   8. **Moderate growth** (12) at $\bar u$: there is $l>0$ with $g^\circ(\cdot,z)(u;h)\le l\|z\|_2^{-m}\exp\big(\|z\|_2^2/(2\|\Sigma^{1/2}\|^2)\big)\|h\|_U$ for all $h\in U$, all $u$ in the open ball of radius $1/l$ about $\bar u$, and all $z$ with $\|z\|_2\ge l$.
--   9. **Aumann integral** (p. 6) of a set-valued $\Phi:V\to 2^H$ with respect to a measure $\mu$: the set of $x\in H$ for which there is a selection $s(v)\in\Phi(v)$ ($\mu$-a.e.) with $v\mapsto\langle s(v),h\rangle$ integrable and $\langle x,h\rangle=\int\langle s(v),h\rangle\,d\mu(v)$ for every $h$.
--
--   These are the objects in which Theorem 2.2, Proposition 2.6 and all results of §§2.2–2.4 are written.
--
--   **Formalization Note** The Clarke derivative uses the denominator $t$; the page prints $h$, a misprint. A real `limsup` is a junk value for functions that are not locally Lipschitz; every use in the mission is at a point where the function is locally Lipschitz (a hypothesis or a proved conclusion). $\rho$ takes values in $[0,\infty]$ (`ℝ≥0∞`); near a point with $g(\bar u,0)<0$ the defining set is $[0,\rho(u,v)]$, as (17) says. The Aumann integral's selections are required to be scalarly integrable (weakly measurable, hence strongly measurable in the separable space $L^2(D)$); this is what makes the integral meaningful.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 3 (Clarke directional derivative, Clarke regularity), pp. 4–6 ((9), Assumption 2.1, (11)–(13), (17), Aumann integral), p. 11 (χ, identification of L²(D)* with L²(D))

import Mathlib

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise MatrixOrder

namespace ChanceStateCtrl.PDE

/-- "`u` is a solution to (P)": `u` is a global minimizer of `F` over the feasible set of (P). -/
def IsSolution {U : Type*} (feasible : Set U) (F : U → ℝ) (u : U) : Prop :=
  u ∈ feasible ∧ ∀ v ∈ feasible, F u ≤ F v

section Clarke

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Clarke's directional derivative (p. 3), with the denominator `t`:
`f°(u; h) = limsup_{u' → u, t ↓ 0} (f(u' + t h) - f(u')) / t`. It is meaningful (and is only used)
for `f` locally Lipschitzian around `u`; otherwise the real `limsup` is a junk value. -/
noncomputable def clarkeDir (f : U → ℝ) (u h : U) : ℝ :=
  limsup (fun q : U × ℝ => (f (q.1 + q.2 • h) - f q.1) / q.2) (𝓝 u ×ˢ 𝓝[>] (0 : ℝ))

/-- `f` is locally Lipschitzian around `u`. -/
def LocLipschitzAt (f : U → ℝ) (u : U) : Prop :=
  ∃ K, ∃ t ∈ 𝓝 u, LipschitzOnWith K f t

/-- The Clarke subdifferential on a real Hilbert space `H`, with `H*` identified with `H` through
the inner product (p. 11): `∂^C f(u) = {y ∈ H | ⟨y, h⟩ ≤ f°(u; h) for all h ∈ H}`. -/
def clarkeSubdiffL2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (u : H) : Set H :=
  {y | ∀ h, inner ℝ y h ≤ clarkeDir f u h}

end Clarke

section Gaussian

variable {m : ℕ}

/-- `Σ^{1/2}` as a linear map of `ℝ^m`: the positive semidefinite square root `CFC.sqrt Σ`, acting on
`EuclideanSpace ℝ (Fin m)` (the root Mathlib's `multivariateGaussian` uses). -/
noncomputable def sigmaRoot (Sigma : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sigma)

/-- The probability function (9): `φ(u) = P(ω | g(u, ξ(ω)) ≤ 0)`. -/
noncomputable def probFn {Ω U : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (u : U) : ℝ :=
  (P {w | g u (ξ w) ≤ 0}).toReal

variable (m) in
/-- The normalizing factor `K` of the chi density: `K = (∫_0^∞ t^{m-1} e^{-t²/2} dt)⁻¹`. -/
noncomputable def chiConst : ℝ :=
  (∫ t in Set.Ioi (0 : ℝ), t ^ (m - 1) * Real.exp (-t ^ 2 / 2))⁻¹

variable (m) in
/-- The density `χ(t) = K t^{m-1} e^{-t²/2}` (`t ≥ 0`) of the chi distribution with `m` degrees
of freedom (p. 11), extended by `0` for `t < 0`. -/
noncomputable def chiDensity (t : ℝ) : ℝ :=
  if 0 ≤ t then chiConst m * t ^ (m - 1) * Real.exp (-t ^ 2 / 2) else 0

variable (m) in
/-- The chi distribution `μ_η` with `m` degrees of freedom, a measure on `ℝ`. -/
noncomputable def chiLaw : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (chiDensity m t))

variable (m) in
/-- The uniform distribution `μ_ζ` on the unit sphere `S^{m-1}` of `ℝ^m`: the surface measure
`volume.toSphere` normalized to total mass one. -/
noncomputable def sphereLaw : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere

/-- The radial probability function (13): `e(u, v) = μ_η{r ≥ 0 | g(u, r Σ^{1/2} v) ≤ 0}` for
`v ∈ S^{m-1}`. -/
noncomputable def radialProb {U : Type*} (g : U → EuclideanSpace ℝ (Fin m) → ℝ)
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (u : U)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : ℝ :=
  (chiLaw m {r | 0 ≤ r ∧ g u (r • sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0}).toReal

/-- The radius function `ρ(u, v) ∈ ℝ ∪ {∞}` of (17), as the supremum (in `[0, ∞]`) of the set
`{r ≥ 0 | g(u, r Σ^{1/2} v) ≤ 0}`; near a point with (10) this set is `[0, ρ(u, v)]`. -/
noncomputable def radius {U : Type*} (g : U → EuclideanSpace ℝ (Fin m) → ℝ)
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (u : U)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : ℝ≥0∞ :=
  ⨆ r ∈ {r : ℝ | 0 ≤ r ∧ g u (r • sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0},
    ENNReal.ofReal r

/-- The condition of moderate growth (12) at `ū`: there is `l > 0` with
`g°(·, z)(u; h) ≤ l ‖z‖^{-m} exp(‖z‖² / (2‖Σ^{1/2}‖²)) ‖h‖` for all `h`, all `u` in the open ball of
radius `1/l` about `ū` and all `z` with `‖z‖ ≥ l`. -/
def ModerateGrowth {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (ubar : U) : Prop :=
  ∃ l : ℝ, 0 < l ∧ ∀ h : U, ∀ u ∈ Metric.ball ubar (1 / l), ∀ z : EuclideanSpace ℝ (Fin m),
    l ≤ ‖z‖ → clarkeDir (fun u' => g u' z) u h ≤
      l * ‖z‖ ^ (-(m : ℤ)) * Real.exp (‖z‖ ^ 2 / (2 * ‖sigmaRoot Sigma‖ ^ 2)) * ‖h‖

end Gaussian

/-- The Aumann integral (p. 6) of a set-valued map `Φ : V → 2^H` into a real Hilbert space `H`
(with `H*` identified with `H`): the set of `x ∈ H` for which there is a selection `s(v) ∈ Φ(v)`
(`μ`-a.e.) whose scalar functions `v ↦ ⟨s(v), h⟩` are integrable and satisfy
`⟨x, h⟩ = ∫ ⟨s(v), h⟩ dμ(v)` for every `h ∈ H`. -/
def aumannL2 {V H : Type*} [MeasurableSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure V) (Φ : V → Set H) : Set H :=
  {x | ∃ s : V → H, (∀ᵐ v ∂μ, s v ∈ Φ v) ∧ (∀ h, Integrable (fun v => inner ℝ (s v) h) μ) ∧
    ∀ h, inner ℝ x h = ∫ v, inner ℝ (s v) h ∂μ}

end ChanceStateCtrl.PDE


