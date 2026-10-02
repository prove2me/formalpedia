-- Prove2me | Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
-- name    : TeschlODE_HigherDim_IsIntegralCurve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:00:07.946987+00:00
-- url     : https://prove2.me/theorems/74259d1b-97ad-4f7b-be82-7c7b1cf52d80
-- title:
--   Integral curve of the autonomous system $\dot x = f(x)$ (6.7) on an open interval
-- statement:
--   Let $E$ be a real normed space (in this mission $E = \mathbb{R}^n$, or the phase space $\mathbb{R}^n \times \mathbb{R}^n$), let $M \subseteq E$ and $f : E \to E$. For a set of times $J \subseteq \mathbb{R}$ and a curve $\varphi : \mathbb{R} \to E$ we say that $\varphi$ is an **integral curve** (a solution) of the autonomous system
--   $$\dot x = f(x) \qquad (6.7)$$
--   **in $M$ on $J$** if $J$ is an open interval (open and order-connected; it may be empty or unbounded), $\varphi(t) \in M$ for every $t \in J$, and $\varphi$ is differentiable at every $t \in J$ with $\dot\varphi(t) = f(\varphi(t))$.
--
--   This is the notion of solution from which the flow of Chapter 6 is built, and Chapter 8 works with that flow throughout.
--
--   **Formalization Note.** $f$ is a total function; only its values on $M$ matter. Solutions live on open intervals, so the derivative is the two-sided `HasDerivAt`; only the values of $\varphi$ on $J$ matter.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eq. (6.7) and the definition of integral curve

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §6.2, p. 189: an integral curve (solution) of the autonomous system `ẋ = f(x)`
(6.7) in `M`, defined on the time set `J`. `J` is an open interval (open and order-connected,
possibly empty or unbounded), `φ` maps `J` into `M`, and `φ` has derivative `f (φ t)` at every
`t ∈ J`. The state space `E` is a real normed space (in this mission `ℝⁿ` or the phase space
`ℝⁿ × ℝⁿ`). Only the values of `φ` on `J` matter. -/
def IsIntegralCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (M : Set E) (J : Set ℝ) (φ : ℝ → E) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t

end TeschlODE.HigherDim


