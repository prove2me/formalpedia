-- Prove2me | Definitions.Def_PhiSobBayes_IsLogConcave
-- name    : PhiSobBayes_IsLogConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:14.979046+00:00
-- url     : https://prove2.me/theorems/dd0972cf-2f80-427b-8429-81c967fa10db
-- title:
--   Log-concave probability measure on $\mathbb R^n$
-- statement:
--   A probability measure $\mu$ on $\mathbb R^n$ is **log-concave** if $\mu(dx)=e^{-V(x)}\,dx$ for a function $V:\mathbb R^n\to\mathbb R$ with $\nabla^2V\succeq0$.
--
--   This is the class of priors in the goal theorem; Lemma 6.1 shows that their Gaussian-channel posteriors are strongly log-concave.
--
--   **Formalization Note** $V$ is twice (Fréchet) differentiable, which $\nabla^2V\succeq0$ presupposes, and $D^2V(x)(v,v)\ge0$ for all $x,v$. The density is with respect to Lebesgue measure on `EuclideanSpace ℝ (Fin n)`. No $C^2$, growth or upper Hessian bound is required.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1.3, p.13 (PDF 13)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `μ` is a **log-concave probability measure** on `ℝⁿ`: `μ(dx) = e^{−V(x)} dx` with `∇²V ⪰ 0`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1.3, p.13 (PDF 13): "We call a probability measure 𝜇 on ℝ𝑛 log-concave if
𝜇(d𝑥) = 𝑒^{−𝑉(𝑥)}d𝑥 with ∇²𝑉 ⪰ 0".

**Formalization Note** `V : ℝⁿ → ℝ` is twice (Fréchet) differentiable, which is what `∇²V ⪰ 0`
presupposes, and its Hessian `D²V(x)(v, v) = fderiv ℝ (fderiv ℝ V) x v v` is positive semidefinite
at every `x`. No `C²`, growth or upper Hessian bound is required. The density is with respect to
Lebesgue measure `volume`. -/
def IsLogConcave {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ V : EuclideanSpace ℝ (Fin n) → ℝ, Differentiable ℝ V ∧
    Differentiable ℝ (fderiv ℝ V) ∧ (∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))

end PhiSobBayes


