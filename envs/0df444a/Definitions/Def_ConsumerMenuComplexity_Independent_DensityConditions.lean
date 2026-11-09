-- Prove2me | Definitions.Def_ConsumerMenuComplexity_Independent_DensityConditions
-- name    : ConsumerMenuComplexity_Independent_DensityConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:03.701023+00:00
-- url     : https://prove2.me/theorems/1df0483b-cedb-4f03-9441-3357708b0a4c
-- title:
--   Lemma 5.2 and Appendix B.1 — genuine densities and F1–F4
-- statement:
--   A density $f:\mathbb R\to\mathbb R$ is measurable and nonnegative, vanishes on the nonpositive half-line, and satisfies $\int f=1$, with normalization expressed by a nonnegative integral. Its law is the corresponding with-density measure mapped to the nonnegative real line.
--
--   F1 requires continuity on $(0,\infty)$ and a locally piecewise $C^1$ description: outside a set with finitely many breakpoints in each compact interval $[a,b]\subset(0,\infty)$ the function is continuously differentiable. It also requires
--   $$vf(v)\longrightarrow0\quad(v\downarrow0\text{ and }v\to\infty),\qquad\mathbb E[V_1]<\infty.$$
--   No boundedness or smoothness at zero is required. F2 states $f(v)+f'(v)\le0$ at each positive point where $f$ is differentiable. For the target curve $r$ and cost $c$, F3 requires $f(v)>0$ at every $0<v<2$ and
--   $$(f(v)+f'(v))r(v)+cf(v)=0\quad\text{a.e. on }(0,2).$$
--   F4 states $f(v)+f'(v)=0$ almost everywhere on $(2,\infty)$. This uses the source footnote-9 convention for differential identities; pointwise positivity is retained. A kink at 2 is permitted. The local $C^1$ formulation makes precise the first-derivative regularity used by the source's piecewise smooth hypothesis, and includes its smooth pieces.
--
--   These predicates describe density regularity without imposing differentiability of any competitor's utility or allocation.
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 5.2, PDF p.17 (printed p.16); §5 footnote 9, PDF p.16 (printed p.15); Lemma B.1 and F1–F4, PDF pp.32–34 (printed pp.31–33)

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Construction
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace ConsumerMenuComplexity.Independent

/-- A genuine probability density on the positive half-line. -/
def IsDensity (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ v, 0 ≤ f v) ∧ (∀ v, v ≤ 0 → f v = 0) ∧
    (∫⁻ v : ℝ, ENNReal.ofReal (f v)) = 1

/-- Piecewise C¹ locally on (0,∞), with finitely many breakpoints on compact
subintervals. In particular, no smoothness or boundedness is imposed at zero. -/
def LocallyPiecewiseSmooth (f : ℝ → ℝ) : Prop :=
  ∃ K : Set ℝ, (∀ a b : ℝ, 0 < a → (K ∩ Set.Icc a b).Finite) ∧
    ContDiffOn ℝ 1 f (Set.Ioi 0 \ K)

def F1 (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi 0) ∧ LocallyPiecewiseSmooth f ∧
    Tendsto (fun v => v * f v) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Tendsto (fun v => v * f v) atTop (nhds 0) ∧
    Integrable (fun v : ℝ≥0 => (v : ℝ)) (densityLaw f)

def F2 (f : ℝ → ℝ) : Prop :=
  ∀ v, 0 < v → DifferentiableAt ℝ f v → f v + deriv f v ≤ 0

/-- Footnote 9: the differential identities are a.e.; positivity is pointwise. -/
def F3 (f : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ v, 0 < v → v < 2 → 0 < f v) ∧
    ∀ᵐ v ∂volume.restrict (Set.Ioo (0 : ℝ) 2),
      (f v + deriv f v) * targetUtility v + c * f v = 0

def F4 (f : ℝ → ℝ) : Prop :=
  ∀ᵐ v ∂volume.restrict (Set.Ioi (2 : ℝ)), f v + deriv f v = 0

end ConsumerMenuComplexity.Independent


