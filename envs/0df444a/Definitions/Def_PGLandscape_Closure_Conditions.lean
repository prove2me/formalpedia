-- Prove2me | Definitions.Def_PGLandscape_Closure_Conditions
-- name    : PGLandscape_Closure_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:36.762149+00:00
-- url     : https://prove2.me/theorems/f8db43c1-3f88-4be6-8895-9874bfcf9089
-- title:
--   Definitions 1–3, Conditions 0, 1, 2.A, 2.B (pp. 8–16) — stationary points, gradient dominance, the policy class Π_Θ, ℓ(θ), the conditions on B, κ_ρ
-- statement:
--   This definition file collects the optimization notions and the structural conditions of Bhandari and Russo, §3 and §5.1.
--
--   **Stationary points (Definition 1).** For $f:\mathbb R^d\to\mathbb R$ and $\mathcal X\subseteq\mathbb R^d$, a point $x\in\mathcal X$ is stationary if $f$ is differentiable at $x$ and
--   $$\langle x'-x,\nabla f(x)\rangle\ge0\qquad\text{for all }x'\in\mathcal X.$$
--
--   **Gradient dominance (Definition 2, (8)).** $f$ is $(c,\mu)$-gradient dominated over $\mathcal X$ ($c>0$, $\mu\ge0$) if for every $x\in\mathcal X$
--   $$\min_{x'\in\mathcal X}f(x')\ \ge\ f(x)+\min_{x'\in\mathcal X}\Big[c\,\langle\nabla f(x),x'-x\rangle+\tfrac\mu2\|x-x'\|_2^2\Big].$$
--
--   **Policy class.** $\Theta\subseteq\mathbb R^d$ is convex, $\theta\mapsto\pi_\theta$ is a parameterization by measurable policies, and $\pi_\theta\in\Pi$ for $\theta\in\Theta$; $\ell(\theta) = \ell(\pi_\theta)$, and $\theta\mapsto\mathcal B(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})$ is the single-period objective of $\pi_\theta$.
--
--   **Conditions.**
--   1. *Condition 0 (differentiability):* for each $\theta\in\Theta$, $(\bar\theta,\theta')\mapsto\mathcal B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ is continuously differentiable on an open set containing $(\theta,\theta)$.
--   2. *Condition 1 (closure under policy improvement):* for each $\pi\in\Pi_\Theta$ there is $\pi^+\in\Pi_\Theta$ with $\mathcal B(\pi^+\mid\eta_\pi,J_\pi) = \min_{\pi'\in\Pi}\mathcal B(\pi'\mid\eta_\pi,J_\pi)$.
--   3. *Condition 2.A:* for each $\pi\in\Pi_\Theta$, $\bar\theta\mapsto\mathcal B(\bar\theta\mid\eta_\pi,J_\pi)$ has no suboptimal stationary points on $\Theta$.
--   4. *Condition 2.B:* for each $\pi\in\Pi_\Theta$ that function is $(c,\mu)$-gradient dominated over $\Theta$.
--
--   **Concentrability (Definition 3, (13)).** A scalar $\kappa$ satisfies (13) if $\|J-J^*\|_{1,\rho}\le\frac{\kappa}{1-\gamma}\|J-TJ\|_{1,\rho}$ for every $J\in\mathcal J_\Theta$; the effective concentrability coefficient $\kappa_\rho$ is the smallest such scalar.
--
--   These conditions are the hypotheses of the paper's landscape theorems.
--
--   **Formalization Note** Stationarity includes differentiability at the point, so the junk gradient $0$ of a non-differentiable function never counts as stationary. Gradient dominance is written without real infima: every lower bound $m$ of the bracket satisfies $f(x)+m\le f(y)$ for all $y\in\mathcal X$. Condition 0 is the joint form that the paper's proof of Lemma 6 (p. 39, "expanding the total derivative in terms of partial derivatives") uses; the printed Condition 0 (p. 13) asks only that the two partial maps $\bar\theta\mapsto\mathcal B(\bar\theta\mid\eta_{\pi_\theta},J_{\pi_\theta})$ and $\bar\theta\mapsto\mathcal B(\theta\mid\eta_{\pi_{\bar\theta}},J_{\pi_\theta})$ be $C^1$, which the joint form implies. The parameterization is defined on all of $\mathbb R^d$ because Condition 0 differentiates at points near $\Theta$. Closedness of $\Theta$ (mentioned in Definition 1) is not imposed. "$\kappa_\rho\le\kappa$" is the predicate that $\kappa$ satisfies (13).
-- source:
--   arXiv:1906.01786v3, Definition 1, p. 8; Definition 2, (8), p. 9; §2, p. 6; Conditions 0, 1, p. 13; Conditions 2.A, 2.B, p. 14; Definition 3, (13), p. 16

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- A stationary point (Definition 1, p. 8) of `f` on `X ⊆ ℝ^d`: `x ∈ X`, `f` is differentiable at
`x`, and `⟨x' − x, ∇f(x)⟩ ≥ 0` for every `x' ∈ X`. -/
def IsStationary {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ X ∧ DifferentiableAt ℝ f x ∧ ∀ x' ∈ X, 0 ≤ inner ℝ (x' - x) (gradient f x)

/-- `(c, µ)`-gradient dominance over `X` (Definition 2, (8), p. 9): `c > 0`, `µ ≥ 0`, and for every
`x ∈ X`, `f` is differentiable at `x` and
`min_{x' ∈ X} f(x') ≥ f(x) + min_{x' ∈ X} [c ⟨∇f(x), x' − x⟩ + (µ/2) ‖x − x'‖₂²]`,
written without real infima: every lower bound `m` of the bracket over `X` satisfies
`f(x) + m ≤ f(y)` for every `y ∈ X`. -/
def IsGradDominated {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (c μ : ℝ) : Prop :=
  0 < c ∧ 0 ≤ μ ∧ ∀ x ∈ X, DifferentiableAt ℝ f x ∧ ∀ y ∈ X, ∀ m : ℝ,
    (∀ x' ∈ X, m ≤ c * inner ℝ (gradient f x) (x' - x) + μ / 2 * ‖x - x'‖ ^ 2) → f x + m ≤ f y

/-- The parameterized policy class `Π_Θ = {π_θ : θ ∈ Θ}` (p. 6): `Θ ⊂ ℝ^d` is convex, the
parameterization `θ ↦ π_θ` is given on all of `ℝ^d` (Condition 0 differentiates at points near `Θ`),
and `π_θ ∈ Π` for `θ ∈ Θ`. -/
def IsPolicyClass {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) : Prop :=
  Convex ℝ Θ ∧ ∀ θ ∈ Θ, IsFeasible M (πθ θ)

/-- The policy gradient objective in the parameter, `ℓ(θ) = ℓ(π_θ)` (p. 6). -/
noncomputable def lossParam {d : ℕ} (M : MDP S A) (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  loss M (πθ θ)

/-- The single-period objective `θ̄ ↦ B(θ̄ | η_{π_θ}, J_{π_θ})` of the policy `π_θ`. -/
noncomputable def piObjective {d : ℕ} (M : MDP S A) (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A)
    (θ θbar : EuclideanSpace ℝ (Fin d)) : ℝ :=
  bellmanObj M (πθ θbar).1 (occupancy M (πθ θ)) (costToGo M (πθ θ))

/-- Condition 0 (Differentiability, p. 13), in the joint form the proof of Lemma 6 (p. 39) uses: for each
`θ ∈ Θ`, `(θ̄, θ') ↦ B(θ̄ | η_{π_θ'}, J_{π_θ})` is continuously differentiable on an open set containing
`(θ, θ)`. Its two partial maps at `(θ, θ)` are the two functions of the printed Condition 0. -/
def Condition0 {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) : Prop :=
  ∀ θ ∈ Θ, ∃ U : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)), IsOpen U ∧ (θ, θ) ∈ U ∧
    ContDiffOn ℝ 1
      (fun p => bellmanObj M (πθ p.1).1 (occupancy M (πθ p.2)) (costToGo M (πθ θ))) U

/-- Condition 1 (Closure under policy improvement, p. 13): for each `π ∈ Π_Θ` there is `π⁺ ∈ Π_Θ`
with `B(π⁺ | η_π, J_π) = min_{π' ∈ Π} B(π' | η_π, J_π)`. -/
def Condition1 {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) : Prop :=
  ∀ θ ∈ Θ, ∃ θplus ∈ Θ, ∀ π' : MPolicy S A, IsFeasible M π' →
    piObjective M πθ θ θplus ≤ bellmanObj M π'.1 (occupancy M (πθ θ)) (costToGo M (πθ θ))

/-- Condition 2.A (p. 14): for each `π ∈ Π_Θ`, `θ̄ ↦ B(θ̄ | η_π, J_π)` has no suboptimal stationary
points on `Θ`. -/
def Condition2A {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) : Prop :=
  ∀ θ ∈ Θ, ∀ θbar, IsStationary (piObjective M πθ θ) Θ θbar →
    ∀ θ' ∈ Θ, piObjective M πθ θ θbar ≤ piObjective M πθ θ θ'

/-- Condition 2.B (p. 14): for each `π ∈ Π_Θ`, `θ̄ ↦ B(θ̄ | η_π, J_π)` is `(c, µ)`-gradient dominated
over `Θ`. -/
def Condition2B {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) (c μ : ℝ) : Prop :=
  ∀ θ ∈ Θ, IsGradDominated (piObjective M πθ θ) Θ c μ

/-- `κ` satisfies (13) (Definition 3, p. 16): `‖J − J*‖_{1,ρ} ≤ κ/(1−γ) ‖J − TJ‖_{1,ρ}` for every
`J ∈ J_Θ`, with `J* = J_{π*}`. The effective concentrability coefficient `κ_ρ` is the smallest such
scalar, so "`κ_ρ ≤ κ`" is exactly `IsConcBound … κ`. -/
def IsConcBound {d : ℕ} (M : MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → MPolicy S A) (πstar : MPolicy S A) (κ : ℝ) : Prop :=
  ∀ θ ∈ Θ, ∫ s, |costToGo M (πθ θ) s - costToGo M πstar s| ∂M.ρ ≤
    κ / (1 - M.γ) * ∫ s, |costToGo M (πθ θ) s - bellmanOpt M (costToGo M (πθ θ)) s| ∂M.ρ

end PGLandscape.Closure


