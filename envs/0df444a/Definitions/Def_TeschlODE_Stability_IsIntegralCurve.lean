-- Prove2me | Definitions.Def_TeschlODE_Stability_IsIntegralCurve
-- name    : TeschlODE_Stability_IsIntegralCurve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:55:19.349153+00:00
-- url     : https://prove2.me/theorems/012c850b-6030-4233-9d03-920695c1fb1a
-- title:
--   Integral curve of the autonomous system $\dot x = f(x)$ (6.7) on an open interval
-- statement:
--   Let $n \in \mathbb{N}$, let $M \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}^n$. For a set of times $J \subseteq \mathbb{R}$ and a curve $\varphi : \mathbb{R} \to \mathbb{R}^n$ we say that $\varphi$ is an **integral curve** (a solution) of the autonomous system
--   $$\dot x = f(x) \qquad (6.7)$$
--   **in $M$ on $J$** if $J$ is an open interval (open and order-connected; it may be empty or unbounded), $\varphi(t) \in M$ for every $t \in J$, and $\varphi$ is differentiable at every $t \in J$ with $\dot\varphi(t) = f(\varphi(t))$.
--
--   This is the notion of "solution $\varphi(t)$" used throughout Chapter 6: the flow is built from these curves (§6.2), and the Liapunov condition (6.36) quantifies over all of them. The initial condition $\varphi(0) = x$ is imposed separately where it is needed.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, so $|x|$ is the Euclidean norm. $f$ is a total function; only its values on $M$ matter, because the curve stays in $M$. Solutions live on open intervals, so the derivative is the two-sided `HasDerivAt`; only the values of $\varphi$ on $J$ matter. A solution on a closed interval extends to an open one (local existence, $M$ open), so nothing is lost.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eq. (6.7) and the definition of integral curve

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.2, p. 189: an integral curve (solution) of the autonomous system
`ẋ = f(x)` (6.7) in `M`, defined on the time set `J`. `J` is an open interval (open and
order-connected, possibly empty or unbounded), `φ` maps `J` into `M`, and `φ` has derivative
`f (φ t)` at every `t ∈ J`. Only the values of `φ` on `J` matter. -/
def IsIntegralCurve {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t

end TeschlODE.Stability


