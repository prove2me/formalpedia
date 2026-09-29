-- Prove2me | Definitions.Def_ConvexOptimization_selfConcordance
-- name    : ConvexOptimization_selfConcordance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T16:11:39.976506+00:00
-- url     : https://prove2.me/theorems/d4551c81-3d8a-4ab5-87cb-f1dd9e907a98
-- title:
--   Self-concordance and the domain-confined damped Newton iteration
-- statement:
--   The vocabulary of the self-concordant Newton analysis of B&V §9.6: the self-concordance property itself, and the damped Newton iteration confined to the domain on which it holds.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}$. Then $f$ is *self-concordant on $\Omega$* when it is convex there, three times continuously differentiable, and every line restriction $\varphi(t) = f(x + tv)$ with $x \in \Omega$, $v \in \mathbb{R}^n$ satisfies
--
--   $$\bigl|\varphi'''(0)\bigr| \;\le\; 2\,\varphi''(0)^{3/2} .$$
--
--   The one-dimensional prototype is $\varphi(t) = -\log t$, for which $\varphi'' = 1/t^{2}$ and $\varphi''' = -2/t^{3}$ give equality — which is why logarithmic barriers are the canonical examples. The condition is *affine invariant*: both sides transform identically under $x \mapsto Tx + s$, so it is a property of the function and not of the coordinates, and every bound derived from it is free of condition numbers.
--
--   Given in addition a gradient field $g$, a Hessian field $H$ assigning to each point a continuous linear map, and backtracking parameters $\alpha, \beta$, a sequence $(x_k)$ is a *damped Newton run on $\Omega$* when for every $k$
--
--   $$x_k \in \Omega, \qquad H(x_k)\,\Delta = -g(x_k), \qquad t \text{ a backtracking step for } f \text{ at } x_k \text{ along } \Delta, \qquad x_{k+1} = x_k + t\,\Delta$$
--
--   for some direction $\Delta$ and step size $t$.
--
--   The two belong together: the confinement to $\Omega$ is not bookkeeping but part of the specification, because a barrier objective $tf_0 + \varphi$ is only defined — and only self-concordant — on the strictly feasible set, and the fact that a full Newton step *stays* inside $\Omega$ is itself a theorem of the self-concordance theory. Together they are the interface against which the mission's Newton-decrement bounds and the $O(\sqrt{m})$ complexity theorem are phrased.
--
--   **Formalization Note** Self-concordance is stated by restriction to lines, via `iteratedDeriv 2` and `iteratedDeriv 3` of `fun t => f (x + t • v)` at $t = 0$ (B&V §9.6.2), so no multilinear third derivative is needed; the exponent $3/2$ is a real power. Statements using it assume `Ω` is open, without which those derivatives carry junk values at boundary points. The Newton direction is characterized by the linear equation rather than by inverting $H$, and backtracking is the predicate of §9.2 published with Mission V, which this module imports.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 496-499, 503, §9.6.1-§9.6.2 (self-concordant functions; self-concordance on R^n by restriction to lines) and §9.6.4 (Newton's method for self-concordant functions, whose iterates stay in the domain)

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Self-concordant on `Ω`** (B&V §9.6.1, lifted to ℝⁿ by line restriction as
in §9.6.2): convex, `C³`, and `|φ'''| ≤ 2 φ''^{3/2}` along every line. -/
def IsSelfConcordantOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ConvexOn ℝ Ω f ∧ ContDiffOn ℝ 3 f Ω ∧
  ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
    |iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0| ≤
      2 * (iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0) ^ ((3 : ℝ) / 2)

/-- Damped-Newton run confined to a domain `Ω` (cf. `IsDampedNewtonSequence`,
Mission V; the confinement is part of the spec since barrier objectives are
only meaningful on `Ω`). -/
def IsDampedNewtonSequenceOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, x k ∈ Ω ∧ ∃ (Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ),
    H (x k) Δ = -g (x k) ∧ IsBacktrackingStep f g α β (x k) Δ t ∧
    x (k + 1) = x k + t • Δ

end ConvexOptimization


