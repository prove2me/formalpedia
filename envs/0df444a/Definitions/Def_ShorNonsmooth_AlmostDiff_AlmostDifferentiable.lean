-- Prove2me | Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
-- name    : ShorNonsmooth_AlmostDiff_AlmostDifferentiable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:49:57.217195+00:00
-- url     : https://prove2.me/theorems/daff8c1a-78c9-48b2-bc72-9854a38a37c8
-- title:
--   Almost differentiable function on $E_n$
-- statement:
--   A function $f : E_n \to \mathbb{R}$ is **almost differentiable** if
--
--   1. in any bounded set $S \subset E_n$ it satisfies the Lipschitz condition: there is $L \ge 0$ (depending on $S$) with $|f(x) - f(y)| \le L\|x - y\|$ for all $x, y \in S$;
--   2. it is differentiable almost everywhere with respect to Lebesgue measure on $E_n$;
--   3. its gradient $\nabla f$ is continuous on its domain $M = \{x \in E_n : f \text{ is differentiable at } x\}$, i.e. the map $x \mapsto \nabla f(x)$ restricted to $M$ is continuous.
--
--   The class contains the continuously differentiable functions and, by Theorem 1.15, the convex functions. It is the class for which Shor defines almost-gradients and runs gradient-type methods for local minimization.
--
--   **Formalization Note** Condition 1 is stated for every bounded set, with a Lipschitz constant depending on the set. Condition 3 is continuity of `gradient f` on the set of points of differentiability, with the subspace topology.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 17, Definition (almost differentiable functions), conditions (a)-(c)

import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 17, Definition: `f : E_n → ℝ` is **almost differentiable** if
(a) in any bounded set it satisfies the Lipschitz condition (the constant may depend on the set);
(b) it is differentiable almost everywhere (Lebesgue measure on `E_n`);
(c) its gradient is continuous on its domain `M`, the set of points where `f` is differentiable
(continuity of the restriction of `∇f` to `M`). -/
def AlmostDifferentiable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ S : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded S →
      ∃ L : NNReal, LipschitzOnWith L f S) ∧
  (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      DifferentiableAt ℝ f x) ∧
  ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x}

end ShorNonsmooth.AlmostDiff


