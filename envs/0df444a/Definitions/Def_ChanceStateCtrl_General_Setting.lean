-- Prove2me | Definitions.Def_ChanceStateCtrl_General_Setting
-- name    : ChanceStateCtrl_General_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:05.875456+00:00
-- url     : https://prove2.me/theorems/7df6815c-fd60-4aa2-ae31-eac62964c999
-- title:
--   §1.1, §2.1, pp. 3–8 — Clarke derivative and subdifferential, probability function φ, Assumption 2.1, condition (12), φ̃ of (20)
-- statement:
--   This module fixes the setting of §2.1 of Geiersbach and Henrion: the general probabilistically constrained problem (9), its standing Assumption 2.1, the nonsmooth calculus it is analysed with, and the convex reformulation (20).
--
--   Let $U$ be a real Banach space with dual $U^*$, let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\xi:\Omega\to\mathbb R^m$ a random vector and $g:U\times\mathbb R^m\to\mathbb R$ a constraint function. The module defines:
--
--   1. **Solutions.** $u^*$ is a solution of $\min\{F(u)\mid u\in C\}$ if $u^*\in C$ and $F(u^*)\le F(u)$ for all $u\in C$ (a global minimizer).
--   2. **Local Lipschitz continuity.** $f:U\to\mathbb R$ is locally Lipschitzian around $u$ if it is Lipschitz on some neighbourhood of $u$.
--   3. **Clarke directional derivative** (p. 3):
--   $$
--   f^\circ(u;h)=\limsup_{u'\to u,\ t\downarrow 0}\frac{f(u'+th)-f(u')}{t}.
--   $$
--   4. **Clarke subdifferential.** $\partial^C f(u)=\{x^*\in U^*\mid \langle x^*,h\rangle\le f^\circ(u;h)\ \forall h\in U\}$.
--   5. **Clarke regularity** (p. 3): $f$ is locally Lipschitzian around $u$ and, for every direction $h$, the one-sided directional derivative $\lim_{t\downarrow0}(f(u+th)-f(u))/t$ exists and equals $f^\circ(u;h)$.
--   6. **Probability function** (9): $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le 0)$.
--   7. **Assumption 2.1** (p. 5), items (i), (iii), (iv): $U$ is a reflexive and separable Banach space; $\xi$ is an $m$-dimensional ($m\ge1$) centered Gaussian random vector with law $\mathcal N(0,\Sigma)$, $\Sigma$ positive definite; $g$ is locally Lipschitzian on $U\times\mathbb R^m$ and $g(u,\cdot)$ is convex for every $u$. Item (ii) ($F$ convex and Fréchet differentiable) is stated in the theorems that involve $F$.
--   8. **Moderate growth condition** (12) at $\bar u$: there is $l>0$ such that
--   $$
--   g^\circ(\cdot,z)(u;h)\le l\,\|z\|_2^{-m}\exp\Big(\frac{\|z\|_2^2}{2\|\Sigma^{1/2}\|^2}\Big)\|h\|_U\qquad\forall h\in U,\ \forall u\in\mathbb B_{1/l}(\bar u),\ \forall z:\ \|z\|_2\ge l .
--   $$
--   9. **The function $\tilde\varphi$ of (20):** $\tilde\varphi(u)=-\log\varphi(u)+\log p$ with $-\log 0=+\infty$, an extended-real-valued function.
--   10. **Convexity of an extended-valued function**: convexity of its epigraph $\{(u,q)\in U\times\mathbb R\mid \tilde\varphi(u)\le q\}$.
--   11. **Subdifferential of convex analysis** of an extended-valued $f$ at a point $u$ where $f(u)$ is finite: $\partial f(u)=\{x^*\in U^*\mid f(u)+\langle x^*,w-u\rangle\le f(w)\ \forall w\in U\}$.
--
--   These are the objects in which the optimality conditions (21) and (22) of Proposition 2.6 are written.
--
--   **Formalization Note** The page writes the Clarke quotient with denominator $h$; this is a misprint for $t$ (with $h$ the quotient is not defined in a Banach space), and the Lean uses $t$. The paper does not define $\partial^C$ itself but refers to Clarke's monograph [10]; the definition above is Clarke's for Banach spaces. $\Sigma^{1/2}$ ("a root of $\Sigma$") is the positive semidefinite square root `CFC.sqrt Sigma`, applied as a continuous linear map on $\mathbb R^m$ — the root Mathlib's `multivariateGaussian` uses — and $\|\Sigma^{1/2}\|$ is its operator norm, which is the same for every root $R$ with $RR^\top=\Sigma$. $\mathbb B_{1/l}(\bar u)$ is read as the open ball. $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`. "$m$-dimensional" is encoded as $m\ge1$. Reflexivity is surjectivity of the canonical embedding $U\to U^{**}$. $\tilde\varphi$ is computed in `EReal` from `ENNReal.log`, whose value at $0$ is $-\infty$, so $-\log 0=+\infty$ exactly as on the page. The convex subdifferential reads $f(u)$ through `EReal.toReal`, so it is meaningful only where $f(u)$ is finite; every theorem using it states that finiteness.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 3–8: §1.1 (p. 3, Clarke directional derivative and regularity), (9) (p. 4), Assumption 2.1 and (12) (p. 5), (20) (p. 7), the subdifferential ∂ (p. 8)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder

namespace ChanceStateCtrl.General

/-- Reflexivity of a real normed space: the canonical embedding into the bidual is onto. -/
def IsReflexive (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ U)

/-- `us` is a solution (a global minimizer) of `min F` over `feasible`. -/
def IsSolution {U : Type*} (feasible : Set U) (F : U → ℝ) (us : U) : Prop :=
  us ∈ feasible ∧ ∀ u ∈ feasible, F us ≤ F u

/-- `f` is locally Lipschitzian around `u`. -/
def LocLipAt {U : Type*} [NormedAddCommGroup U] (f : U → ℝ) (u : U) : Prop :=
  ∃ K : NNReal, ∃ t ∈ 𝓝 u, LipschitzOnWith K f t

/-- The Clarke directional derivative `f⁰(u; h) = limsup_{u' → u, t ↓ 0} (f(u' + t h) - f(u')) / t`
(p. 3, with the denominator `t`). -/
noncomputable def clarkeDir {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → ℝ) (u h : U) : ℝ :=
  limsup (fun q : U × ℝ => (f (q.1 + q.2 • h) - f q.1) / q.2) (𝓝 u ×ˢ 𝓝[>] (0 : ℝ))

/-- The Clarke subdifferential `∂^C f(u) = {x* ∈ U* | ⟨x*, h⟩ ≤ f⁰(u; h) ∀ h}`. -/
def clarkeSubdiff {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → ℝ) (u : U) : Set (StrongDual ℝ U) :=
  {x | ∀ h, x h ≤ clarkeDir f u h}

/-- Clarke regularity at `u` (p. 3): `f` is locally Lipschitzian around `u` and, for every direction
`h`, the one-sided directional derivative `lim_{t ↓ 0} (f(u + t h) - f(u)) / t` exists and equals
`f⁰(u; h)`. -/
def IsClarkeRegularAt {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → ℝ) (u : U) : Prop :=
  LocLipAt f u ∧ ∀ h : U,
    Tendsto (fun t : ℝ => (f (u + t • h) - f u) / t) (𝓝[>] (0 : ℝ)) (𝓝 (clarkeDir f u h))

/-- The probability function `φ(u) = P(ω | g(u, ξ(ω)) ≤ 0)` of (9). -/
noncomputable def probFn {Ω U : Type*} {m : ℕ} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (u : U) : ℝ :=
  (P {ω | g u (ξ ω) ≤ 0}).toReal

/-- The root `Σ^{1/2}` of the covariance matrix, as a continuous linear map on `ℝᵐ`
(the positive semidefinite square root, the one used by `multivariateGaussian`). -/
noncomputable def sqrtCov {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sigma)

/-- Assumption 2.1 (i), (iii), (iv) (p. 5): `U` is a reflexive separable Banach space; `ξ` is an
`m`-dimensional (`m ≥ 1`) centered Gaussian vector `N(0, Σ)` with nondegenerate `Σ` on a probability
space; `g` is locally Lipschitzian on `U × ℝᵐ` and convex in its second argument. Item (ii), on the
objective `F`, is stated separately in the theorems that involve `F`. -/
structure Assumption21 {Ω U : Type*} {m : ℕ} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m))
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (g : U → EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  complete : CompleteSpace U
  separable : TopologicalSpace.SeparableSpace U
  reflexive : IsReflexive U
  isProb : IsProbabilityMeasure P
  dim_pos : 0 < m
  measurable_xi : Measurable ξ
  posDef : Sigma.PosDef
  law : P.map ξ = multivariateGaussian 0 Sigma
  locLip : LocallyLipschitz (Function.uncurry g)
  convex_snd : ∀ u, ConvexOn ℝ Set.univ (g u)

/-- The moderate growth condition (12) at `ub`: there is `l > 0` such that
`g°(·, z)(u; h) ≤ l ‖z‖^{-m} exp(‖z‖² / (2 ‖Σ^{1/2}‖²)) ‖h‖` for all `h ∈ U`, all `u` in the open
ball `B_{1/l}(ub)` and all `z` with `‖z‖ ≥ l`. -/
def ModerateGrowth {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (ub : U) : Prop :=
  ∃ l : ℝ, 0 < l ∧ ∀ h : U, ∀ u ∈ Metric.ball ub (1 / l), ∀ z : EuclideanSpace ℝ (Fin m),
    l ≤ ‖z‖ →
      clarkeDir (fun w => g w z) u h ≤
        l * ‖z‖ ^ (-(m : ℤ)) * Real.exp (‖z‖ ^ 2 / (2 * ‖sqrtCov Sigma‖ ^ 2)) * ‖h‖

/-- The extended-valued function `φ̃(u) = -log φ(u) + log p` of (20), with `-log 0 = +∞`
(computed in `EReal` from `ENNReal.log`, for which `log 0 = ⊥`). -/
noncomputable def phiTilde {Ω U : Type*} {m : ℕ} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (p : ℝ) (u : U) :
    EReal :=
  -(ENNReal.log (P {ω | g u (ξ ω) ≤ 0})) + (Real.log p : EReal)

/-- Convexity of an extended-valued function `f : U → ℝ ∪ {±∞}`: its epigraph
`{(u, q) ∈ U × ℝ | f(u) ≤ q}` is convex. -/
def ConvexEpi {U : Type*} [AddCommGroup U] [Module ℝ U] (f : U → EReal) : Prop :=
  Convex ℝ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)}

/-- The subdifferential of convex analysis of an extended-valued `f` at a point `u` where `f(u)` is
finite: `∂f(u) = {x* ∈ U* | f(u) + ⟨x*, w - u⟩ ≤ f(w) ∀ w ∈ U}`. -/
def convexSubdiffE {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → EReal) (u : U) : Set (StrongDual ℝ U) :=
  {x | ∀ w : U, (((f u).toReal + x (w - u) : ℝ) : EReal) ≤ f w}

end ChanceStateCtrl.General


