-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory
-- name    : NonsmoothLojasiewicz_Traj_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:49.369075+00:00
-- url     : https://prove2.me/theorems/bfb7a76c-e647-4d69-9b18-fef12439c534
-- title:
--   Trajectories and maximal trajectories of the subgradient system $\dot x(t)+\partial f(x(t))\ni 0$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ with limiting subdifferential $\partial f$, and let $T\in(0,+\infty]$.
--
--   A **trajectory** of the subgradient dynamical system $(\mathcal G)$ on $[0,T)$ is an absolutely continuous curve $x:[0,T)\to\mathbb R^n$ such that
--   $$\begin{cases}\dot x(t)+\partial f(x(t))\ni 0 & \text{for almost every } t\in(0,T),\\ \partial f(x(t))\neq\emptyset & \text{for all } t\in[0,T),\end{cases}$$
--   "almost every" referring to Lebesgue measure on $\mathbb R$. A trajectory is **maximal** if there is no extension of its domain compatible with $(\mathcal G)$: no trajectory on a longer interval $[0,T')$, $T'>T$, coincides with $x$ on $[0,T)$.
--
--   These are the objects of Theorems 4.5 and 4.7: bounded maximal trajectories are shown to have finite length and to converge to a critical point at a rate governed by the Łojasiewicz exponent.
--
--   **Formalization Note** Curves are functions $\mathbb R\to\mathbb R^n$ whose values outside $[0,T)$ play no role; $T$ lives in $[0,+\infty]$ (`ℝ≥0∞`), $T=+\infty$ meaning $[0,+\infty)$. "Absolutely continuous on $[0,T)$" means absolutely continuous on every compact $[0,b]\subseteq[0,T)$ (the $W^{1,1}_{\mathrm{loc}}$ reading of Brézis, and the only meaningful one for $T=+\infty$). The inclusion is written as: for almost every $t\in(0,T)$, $x$ is differentiable at $t$ with derivative $v$ and $-v\in\partial f(x(t))$. `timeDom T` denotes $[0,T)$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1217, Section 4, system (G) and the definition of a maximal trajectory

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open MeasureTheory
open scoped ENNReal

namespace NonsmoothLojasiewicz.Traj

open NonconvexSplitting.Shared

/-- The time interval `[0, T)` for `T ∈ (0, +∞]` (`T = ⊤` gives `[0, +∞)`). -/
def timeDom (T : ℝ≥0∞) : Set ℝ := {t | 0 ≤ t ∧ ENNReal.ofReal t < T}

/-- A trajectory of the subgradient dynamical system (𝒢) (p. 1217) on `[0, T)`: a curve
`x : [0, T) → ℝⁿ`, absolutely continuous on every compact `[0, b] ⊆ [0, T)`, such that
`ẋ(t) + ∂f(x(t)) ∋ 0` for almost every `t ∈ (0, T)` (Lebesgue measure) and
`∂f(x(t)) ≠ ∅` for every `t ∈ [0, T)`. Values of `x` outside `[0, T)` play no role. -/
def IsTrajectory {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) : Prop :=
  0 < T ∧
  (∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b < T → AbsolutelyContinuousOnInterval x 0 b) ∧
  (∀ᵐ t : ℝ, 0 < t → ENNReal.ofReal t < T →
    ∃ v, HasDerivAt x v t ∧ -v ∈ LimitingSubdiff f (x t)) ∧
  (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < T → (LimitingSubdiff f (x t)).Nonempty)

/-- A trajectory is *maximal* (p. 1217) if there is no extension of its domain compatible with
(𝒢): no trajectory `y` on a longer interval `[0, T')`, `T' > T`, agreeing with `x` on `[0, T)`. -/
def IsMaximalTrajectory {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) : Prop :=
  IsTrajectory f x T ∧
  ¬ ∃ T' : ℝ≥0∞, T < T' ∧ ∃ y : ℝ → EuclideanSpace ℝ (Fin n),
    (∀ t ∈ timeDom T, y t = x t) ∧ IsTrajectory f y T'

end NonsmoothLojasiewicz.Traj


