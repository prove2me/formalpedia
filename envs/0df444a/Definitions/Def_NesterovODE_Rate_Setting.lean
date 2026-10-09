-- Prove2me | Definitions.Def_NesterovODE_Rate_Setting
-- name    : NesterovODE_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:17.544043+00:00
-- url     : https://prove2.me/theorems/75ee68b9-d0c2-4fdc-980d-7e114240261a
-- title:
--   (3), p. 2, and §1.3, p. 5 — the classes F_L and F_∞, solutions of Ẍ + (r/t)Ẋ + ∇f(X) = 0 with X(0) = x₀, Ẋ(0) = 0, and the energy E(t)
-- statement:
--   This module fixes the objects of §3.1 of Su, Boyd and Candès.
--
--   Throughout, $\mathbb R^n$ carries the Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$, and $\nabla f$ denotes the gradient of $f:\mathbb R^n\to\mathbb R$.
--
--   1. **The class $\mathcal F_L$** (p. 5). For $L>0$, $f\in\mathcal F_L$ if $f$ is convex, continuously differentiable, and
--   $$\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n .$$
--   2. **The class $\mathcal F_\infty$** (p. 6): $\mathcal F_\infty=\bigcup_{L>0}\mathcal F_L$.
--   3. **Solutions of the ODE.** For $r\in\mathbb R$ and $x_0\in\mathbb R^n$, a pair $(X,V)$ of curves is a solution of
--   $$\ddot X+\frac rt\dot X+\nabla f(X)=0\qquad(t>0),\qquad X(0)=x_0,\ \dot X(0)=0,$$
--   if $X(0)=x_0$, $V(0)=0$, $X$ has right derivative $V(0)$ at $t=0$ and $V$ is right-continuous at $0$, and for every $t>0$, $X$ is differentiable at $t$ with $\dot X(t)=V(t)$ and $V$ is differentiable at $t$ with
--   $$\dot V(t)=-\frac rt V(t)-\nabla f(X(t)).$$
--   The case $r=3$ is the ODE (3) of p. 2, the continuous-time limit of Nesterov's accelerated gradient method.
--   4. **The energy** (p. 7). For a point $x^\star$ and $f^\star=f(x^\star)$,
--   $$\mathcal E(t)=t^2\big(f(X(t))-f^\star\big)+2\Big\|X(t)+\frac t2\dot X(t)-x^\star\Big\|^2 .$$
--
--   These are the objects of Theorem 3 and its proof: the energy is the Lyapunov function whose monotonicity yields the $O(1/t^2)$ rate.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the solution predicate is stated on a general real Hilbert space. The velocity $\dot X$ is carried as a second curve $V$, with all derivatives as `HasDerivAt`/`HasDerivWithinAt` facts. For continuous $\nabla f$ this is exactly membership in $C^2((0,\infty))\cap C^1([0,\infty))$ (p. 6) together with the ODE and the initial conditions. Values for $t<0$ are unconstrained and play no role.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, pp. 2, 5, 6, 7: (3), §1.3, Theorem 1, proof of Theorem 3

import Mathlib

namespace NesterovODE.Rate

/-- The class `F_L` (arXiv:1503.01243v2, p. 5): `f : ℝⁿ → ℝ` is convex, continuously
differentiable, and its gradient is `L`-Lipschitz for the Euclidean norm, with `L > 0`. -/
def IsFL {n : ℕ} (L : NNReal) (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  0 < L ∧ ConvexOn ℝ Set.univ f ∧ ContDiff ℝ 1 f ∧ LipschitzWith L (gradient f)

/-- The class `F_∞ = ⋃_{L > 0} F_L` (p. 6, Theorem 1). -/
def IsFinfty {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ L : NNReal, IsFL L f

/-- `X` solves `Ẍ + (r/t) Ẋ + ∇f(X) = 0` on `(0, ∞)` with `X(0) = x₀`, `Ẋ(0) = 0`, and
`X ∈ C²((0,∞)) ∩ C¹([0,∞))`; `V` is the velocity `Ẋ`. (ODE (3) of p. 2 is the case `r = 3`.) -/
def IsSolution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (r : ℝ) (x₀ : E) (X V : ℝ → E) : Prop :=
  X 0 = x₀ ∧ V 0 = 0 ∧
  HasDerivWithinAt X (V 0) (Set.Ici 0) 0 ∧ ContinuousWithinAt V (Set.Ici 0) 0 ∧
  ∀ t : ℝ, 0 < t → HasDerivAt X (V t) t ∧
    HasDerivAt V (-(r / t) • V t - gradient f (X t)) t

/-- The energy functional of the proof of Theorem 3 (p. 7):
`E(t) = t²(f(X(t)) − f⋆) + 2‖X(t) + t Ẋ(t)/2 − x⋆‖²`, with `f⋆ = f(x⋆)` and `Ẋ = V`. -/
noncomputable def energy {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  t ^ 2 * (f (X t) - f xstar) + 2 * ‖X t + (t / 2) • V t - xstar‖ ^ 2

end NesterovODE.Rate


