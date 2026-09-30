-- Prove2me | Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
-- name    : NonconvexSplitting_ADMMKL_KLProperty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T18:08:13.255985+00:00
-- url     : https://prove2.me/theorems/5eae934f-7240-4961-8baf-1b9af37b558e
-- title:
--   Kurdyka–Łojasiewicz property and KL functions
-- statement:
--   Let $X$ be a real inner product space and $f:X\to(-\infty,+\infty]$ proper. $f$ has the **Kurdyka–Łojasiewicz (KL) property** at $\hat x\in\operatorname{dom}\partial f$ if there are $\eta>0$, a neighbourhood $V$ of $\hat x$ and a function $\varphi:[0,\eta)\to\mathbb R_+$ such that
--
--   1. $\varphi$ is continuous and concave, $\varphi(0)=0$, and $\varphi$ is continuously differentiable on $(0,\eta)$ with $\varphi'>0$ there;
--   2. for every $x\in V$ with $f(\hat x)<f(x)<f(\hat x)+\eta$,
--   $$
--   \varphi'\bigl(f(x)-f(\hat x)\bigr)\,\operatorname{dist}\bigl(0,\partial f(x)\bigr)\ge1 .
--   $$
--
--   A proper closed $f$ with the KL property at every point of $\operatorname{dom}\partial f$ is a **KL function**.
--
--   The KL inequality is the tool that upgrades subsequential convergence of descent-type methods to convergence of the whole sequence.
--
--   **Formalization Note** Condition 2 is stated as $\varphi'(f(x)-f(\hat x))\,\|v\|\ge1$ for **every** $v\in\partial f(x)$, which is the displayed inequality with $\operatorname{dist}(0,\emptyset)=+\infty$ (Mathlib's `infDist` to the empty set is $0$, which would be wrong). The paper allows $\eta\in(0,\infty]$; here $\eta$ is a positive real, which is equivalent (shrink $\eta=\infty$ to $\eta=1$). $\varphi$ is a function $\mathbb R\to\mathbb R$ constrained only on $[0,\eta)$; $\varphi'$ is `deriv φ`, meaningful on the open interval where $\varphi$ is $C^1$. The difference $f(x)-f(\hat x)$ is a finite real under the two strict bounds.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, pp. 4–5, Definition 1 (KL property & KL function)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open NonconvexSplitting.Shared

open Filter Topology

namespace NonconvexSplitting.ADMMKL

/-- Condition (ii) of Definition 1 of Li–Pong (p. 5) for given `η`, `V`, `φ`: for every `x ∈ V`
with `f(x̂) < f(x) < f(x̂) + η` and every `v ∈ ∂f(x)` (limiting subdifferential),
`φ'(f(x) - f(x̂)) ‖v‖ ≥ 1`. Quantifying over all `v ∈ ∂f(x)` is the inequality
`φ'(f(x) - f(x̂)) dist(0, ∂f(x)) ≥ 1` with the convention `dist(0, ∅) = +∞`.
Under the two strict bounds `f(x) - f(x̂)` is a finite real number in `(0, η)`. -/
def KLIneq {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (xhat : X) (η : ℝ) (V : Set X) (φ : ℝ → ℝ) : Prop :=
  ∀ x ∈ V, f xhat < f x → f x < f xhat + (η : EReal) →
    ∀ v ∈ LimitingSubdiff f x, 1 ≤ deriv φ (f x - f xhat).toReal * ‖v‖

/-- Condition (i) of Definition 1 of Li–Pong (pp. 4–5) on the desingularizing function:
`φ : [0, η) → ℝ₊` is continuous and concave, `φ(0) = 0`, and `φ` is continuously
differentiable on `(0, η)` with positive derivative. (Values of `φ` outside `[0, η)` are
irrelevant.) -/
def IsDesingularizer (η : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Ico 0 η) ∧ ConcaveOn ℝ (Set.Ico 0 η) φ ∧
    (∀ s ∈ Set.Ico 0 η, 0 ≤ φ s) ∧ φ 0 = 0 ∧
    ContDiffOn ℝ 1 φ (Set.Ioo 0 η) ∧ ∀ s ∈ Set.Ioo 0 η, 0 < deriv φ s

/-- The Kurdyka–Łojasiewicz (KL) property of `f` at `x̂` (Definition 1 of Li–Pong, pp. 4–5):
there are `η > 0`, a neighbourhood `V` of `x̂` and a function `φ` satisfying (i) such that (ii)
holds. The definition is used at points `x̂ ∈ dom ∂f`. -/
def HasKLProperty {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (xhat : X) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ V ∈ 𝓝 xhat, ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧ KLIneq f xhat η V φ

/-- A KL function (Definition 1 of Li–Pong, p. 5): a proper closed (lower semicontinuous)
function with values in `(-∞, +∞]` that has the KL property at every point of
`dom ∂f = {x | ∂f(x) ≠ ∅}`. -/
def IsKLFunction {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) : Prop :=
  IsProperFn f ∧ LowerSemicontinuous f ∧
    ∀ xhat, (LimitingSubdiff f xhat).Nonempty → HasKLProperty f xhat

end NonconvexSplitting.ADMMKL


