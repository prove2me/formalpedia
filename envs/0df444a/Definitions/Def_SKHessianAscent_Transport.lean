-- Prove2me | Definitions.Def_SKHessianAscent_Transport
-- name    : SKHessianAscent_Transport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:57:10.931094+00:00
-- url     : https://prove2.me/theorems/818fe5e0-fee9-4473-90a9-450db701b331
-- title:
--   Definition 3.10 — Wasserstein distance $d_{W,p}$, the transportation inequality $T_p$, and path laws on $C^0([0,T],\mathbb R^n)$
-- statement:
--   Let $(E,d)$ be a metric space with its Borel $\sigma$-algebra.
--
--   - `couplings μ ν` is $\Sigma(\mu,\nu)$, the set of measures $\pi$ on $E\times E$ whose first marginal is $\mu$ and whose second marginal is $\nu$.
--   - `wass p μ ν` is the Wasserstein distance
--   $$d_{W,p}(\mu,\nu)=\inf_{\pi\in\Sigma(\mu,\nu)}\Big(\int d(x,y)^p\,d\pi(x,y)\Big)^{1/p}\in[0,\infty].$$
--   - **Definition 3.10.** `SatisfiesT p C P`: the measure $P$ satisfies the $T_p$ transportation inequality with constant $C$, that is,
--   $$d_{W,p}(P,\mu)^2\le 2C\,H(\mu\mid P)\qquad\text{for every probability measure }\mu\text{ on }E,$$
--   where $H(\mu\mid P)\in[0,\infty]$ is the relative entropy.
--   - `pathOf T X ω` is the path $(X_t(\omega))_{0\le t\le T}$ of a process $X$ with values in $\mathbb R^n$, as a point of $C^0([0,T],\mathbb R^n)$ with the uniform norm $\|x\|_\infty=\sup_{0\le t\le T}\|x_t\|_2$, and `pathLaw P T X` is its law under $P$.
--
--   **Formalization Note** Relative entropy is Mathlib's `InformationTheory.klDiv`, which is $+\infty$ unless $\mu\ll P$ with integrable log-density, so the inequality is between elements of $[0,\infty]$. The path space is the published `SKWeakPoincare.PathSpace`. `pathOf` is the zero path at sample points where $t\mapsto X_t(\omega)$ is not continuous on $[0,T]$; the processes of the mission have continuous paths.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.4, Definition 3.10, p. 15; the Wasserstein distance as in [DLSS26a, Definition 6.10] (https://arxiv.org/abs/2605.03718, p. 106)

import Mathlib
import Definitions.Def_SKWeakPoincare_PathSpace

open MeasureTheory
open scoped ENNReal NNReal

namespace SKHessianAscent

/-!
# Wasserstein distance, transportation inequalities and path laws

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §3.4, Definition 3.10 (p. 15): "A probability measure `P` on a metric space
satisfies a `T_p` transportation inequality with constant `C` if `d_{W,p}(P, μ)² ≤ 2C H(μ | P)` for
every probability measure `μ`, where `d_{W,p}` denotes Wasserstein distance and `H` relative
entropy." The Wasserstein distance is the one of the definition the paper restates,
[DLSS26a, Definition 6.10] (arXiv:2605.03718, p. 106):
`W_p(μ, ν) = inf_{π ∈ Σ(μ,ν)} (∫ d(x, y)^p dπ(x, y))^{1/p}`, with `Σ(μ, ν)` the measures on `E × E`
with first marginal `μ` and second marginal `ν`.

**Formalization Note.** Relative entropy is Mathlib's `InformationTheory.klDiv` (values in
`[0, ∞]`, equal to `∞` unless `μ ≪ P` with integrable log-likelihood ratio), so the inequality is
between extended nonnegative reals. The path space `C⁰([0, T], ℝⁿ)` with the uniform Euclidean
norm is the published `SKWeakPoincare.PathSpace`.
-/

/-- The couplings `Σ(μ, ν)`: measures on `E × E` with marginals `μ` and `ν`. -/
def couplings {E : Type*} [MeasurableSpace E] (μ ν : Measure E) : Set (Measure (E × E)) :=
  {π | π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- The Wasserstein distance `d_{W,p}(μ, ν) = inf_{π ∈ Σ(μ,ν)} (∫ d(x,y)^p dπ)^{1/p}`, with values
in `[0, ∞]`. -/
noncomputable def wass {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] (p : ℝ)
    (μ ν : Measure E) : ℝ≥0∞ :=
  (⨅ π ∈ couplings μ ν, ∫⁻ z, edist z.1 z.2 ^ p ∂π) ^ (1 / p)

/-- Definition 3.10: `P` satisfies the `T_p` transportation inequality with constant `C`:
`d_{W,p}(P, μ)² ≤ 2C H(μ | P)` for every probability measure `μ`. -/
def SatisfiesT {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] (p C : ℝ)
    (P : Measure E) : Prop :=
  ∀ μ : Measure E, IsProbabilityMeasure μ →
    wass p P μ ^ 2 ≤ ENNReal.ofReal (2 * C) * InformationTheory.klDiv μ P

/-- The path `(X_t)_{0 ≤ t ≤ T}` of a process with time `ℝ≥0`, as a point of `C⁰([0, T], ℝⁿ)`
(the zero path when the restriction to `[0, T]` is not continuous). -/
noncomputable def pathOf {Ω : Type*} {n : ℕ} (T : ℝ)
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) : SKWeakPoincare.PathSpace T n :=
  open Classical in
  if h : Continuous (fun t : Set.Icc (0 : ℝ) T => X ⟨(t : ℝ), t.2.1⟩ ω) then ⟨_, h⟩ else 0

/-- The path law on `C⁰([0, T], ℝⁿ)` of a process `X` on `(Ω, P)`. -/
noncomputable def pathLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (T : ℝ)
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)) : Measure (SKWeakPoincare.PathSpace T n) :=
  P.map (pathOf T X)

end SKHessianAscent


