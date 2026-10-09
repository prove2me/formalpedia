-- Prove2me | Definitions.Def_NesterovODE_WellPosed_Setting
-- name    : NesterovODE_WellPosed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:29.620304+00:00
-- url     : https://prove2.me/theorems/56e19bd9-3b42-47f2-9a50-056802ba0089
-- title:
--   (3), p. 2; §1.3, p. 5; (31), p. 28 — smooth convex objectives and singular and smoothed ODE solutions
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$. For $L>0$, the paper's class $\mathcal F_L$ consists of convex, continuously differentiable functions with
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\qquad(x,y\in\mathbb R^n).
--   $$
--   A pair of position and velocity paths $(X,V)$ is a solution with initial point $x_0$ when $V=\dot X$, $X(0)=x_0$, $V(0)=0$, and
--   $$
--   \dot V(t)+\frac r t V(t)+\nabla f(X(t))=0\qquad(t>0).
--   $$
--   The paper's equation (3) is the case $r=3$. A local solution satisfies the same equation with $r=3$ for $0<t<a$, where $a>0$. For $\delta>0$, a smoothed solution satisfies equation (31), with damping $3/\max(\delta,t)$, on $[0,\infty)$.
--
--   These predicates fix the objective class and the regularity of trajectories used in the well-posedness argument.
--
--   **Formalization Note** The space is Euclidean $\mathbb R^n$. At time zero, $X$ has a right derivative equal to $V(0)=0$, and $V$ is right continuous. Both paths have the derivatives specified by the ODE for positive time. The smoothed solution uses right derivatives at zero. Values at negative times play no role; the equation is never evaluated with $t=0$ in the singular case.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, pp. 2, 5, 28, (3), §1.3, (31)

import Mathlib

namespace NesterovODE.WellPosed

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The paper's class F_L of convex C¹ functions with an L-Lipschitz gradient, L > 0. -/
def IsFL {n : ℕ} (f : E n → ℝ) (L : NNReal) : Prop :=
  0 < L ∧ ConvexOn ℝ Set.univ f ∧ ContDiff ℝ 1 f ∧ LipschitzWith L (gradient f)

/-- The singular equation (3) on t > 0 with its one-sided initial conditions. -/
def IsSolution {n : ℕ} (f : E n → ℝ) (r : ℝ) (x₀ : E n)
    (X V : ℝ → E n) : Prop :=
  X 0 = x₀ ∧ V 0 = 0 ∧
  HasDerivWithinAt X (V 0) (Set.Ici 0) 0 ∧
  ContinuousWithinAt V (Set.Ici 0) 0 ∧
  ∀ t : ℝ, 0 < t →
    HasDerivAt X (V t) t ∧
    HasDerivAt V (-(r / t) • V t - gradient f (X t)) t

/-- Equation (3) on a right neighborhood [0,a) of its singular initial time. -/
def IsLocalSolution {n : ℕ} (f : E n → ℝ) (x₀ : E n) (a : ℝ)
    (X V : ℝ → E n) : Prop :=
  0 < a ∧ X 0 = x₀ ∧ V 0 = 0 ∧
  HasDerivWithinAt X (V 0) (Set.Ici 0) 0 ∧
  ContinuousWithinAt V (Set.Ici 0) 0 ∧
  ∀ t : ℝ, 0 < t → t < a →
    HasDerivAt X (V t) t ∧
    HasDerivAt V (-(3 / t) • V t - gradient f (X t)) t

/-- The smoothed equation (31) with δ > 0 and derivatives on [0,∞). -/
def IsSmoothedSolution {n : ℕ} (f : E n → ℝ) (δ : ℝ) (x₀ : E n)
    (X V : ℝ → E n) : Prop :=
  0 < δ ∧ X 0 = x₀ ∧ V 0 = 0 ∧
  ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt X (V t) (Set.Ici 0) t ∧
    HasDerivWithinAt V (-(3 / max δ t) • V t - gradient f (X t)) (Set.Ici 0) t

end NesterovODE.WellPosed


