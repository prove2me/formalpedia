-- Prove2me | Definitions.Def_DoCarmo_plane_curves
-- name    : DoCarmo_plane_curves
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T01:20:05.265559+00:00
-- url     : https://prove2.me/theorems/b798ae6e-12e5-4756-9544-827976a1023c
-- title:
--   Closed and simple plane curves, signed curvature, area, convexity, vertices
-- statement:
--   The vocabulary of do Carmo §1-7, the global theory of plane curves.
--
--   A **closed plane curve** of length $l$ is a regular curve $\alpha$ whose derivatives of all orders agree at the endpoints of $[0,l]$; equivalently, as formalized here, a smooth $l$-periodic map $\mathbb{R} \to \mathbb{R}^2$ of unit speed. It is **simple** when $\alpha(t_1) \neq \alpha(t_2)$ for distinct $t_1, t_2 \in [0,l)$.
--
--   With $J$ the rotation by $+\pi/2$, the **signed curvature** is $k(s) = \langle \alpha''(s), J\alpha'(s)\rangle$ (do Carmo §1-5, Remark 1), a **vertex** is a parameter with $k'(t) = 0$, and the curve is **convex** when for each $t$ its whole trace lies in one closed half-plane bounded by the tangent line at $t$.
--
--   The **area** bounded by a positively oriented simple closed curve is taken from do Carmo's equation (1) of §1-7:
--
--   $$ A = \frac12 \int_0^l (x y' - y x')\,dt . $$
--
--   Finally an **angle function** is a smooth $\theta$ with $\alpha'(s) = (\cos\theta(s), \sin\theta(s))$; the rotation index of the curve is $(\theta(l)-\theta(0))/2\pi$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Mathlib

namespace DoCarmoDG

/-- Rotation by `+π/2` in `ℝ²`: `rot90 (a, b) = (-b, a)`.  It sends the unit tangent `t` of a
plane curve to the normal `n` for which `{t, n}` has the orientation of the natural basis
(do Carmo §1-5, Remark 1). -/
noncomputable def rot90 (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-w 1, w 0]

/-- A closed plane curve of period `l`, parametrized by arc length (do Carmo §1-7):
`α` is smooth, `l`-periodic — so that `α` and all its derivatives agree at the endpoints of
`[0, l]` — and has unit speed, so that `l` is its length. -/
def IsClosedUnitSpeedCurve (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  0 < l ∧ ContDiff ℝ (⊤ : ℕ∞) α ∧ (∀ t, α (t + l) = α t) ∧ ∀ t, ‖deriv α t‖ = 1

/-- A simple closed plane curve: a closed curve without further self-intersections
(do Carmo §1-7). -/
def IsSimpleClosedCurve (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  IsClosedUnitSpeedCurve l α ∧
    ∀ t₁ ∈ Set.Ico (0 : ℝ) l, ∀ t₂ ∈ Set.Ico (0 : ℝ) l, t₁ ≠ t₂ → α t₁ ≠ α t₂

/-- The signed curvature of a plane curve parametrized by arc length, defined by
`α'' = k · rot90 α'` (do Carmo §1-5, Remark 1). -/
noncomputable def signedCurvature (α : ℝ → EuclideanSpace ℝ (Fin 2)) (s : ℝ) : ℝ :=
  inner ℝ (deriv (deriv α) s) (rot90 (deriv α s))

/-- The area bounded by a positively oriented simple closed curve, do Carmo §1-7, Eq. (1):
`A = ½ ∫ (x y' - y x') dt`. -/
noncomputable def signedArea (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..l, (α t 0 * deriv α t 1 - α t 1 * deriv α t 0)

/-- A convex plane curve: for every parameter, the whole trace lies in one of the two closed
half-planes determined by the tangent line at that parameter (do Carmo §1-7). -/
def IsConvexPlaneCurve (α : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ t, (∀ u, 0 ≤ inner ℝ (α u - α t) (rot90 (deriv α t))) ∨
       (∀ u, inner ℝ (α u - α t) (rot90 (deriv α t)) ≤ 0)

/-- A vertex of a plane curve: a parameter where the derivative of the curvature vanishes
(do Carmo §1-7). -/
def IsVertex (α : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : Prop :=
  deriv (signedCurvature α) t = 0

/-- An angle function (a differentiable lift of the tangent indicatrix) of a plane curve
parametrized by arc length: `α'(s) = (cos θ(s), sin θ(s))` (do Carmo §1-7). -/
def IsAngleFunction (α : ℝ → EuclideanSpace ℝ (Fin 2)) (theta : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) theta ∧ ∀ s, deriv α s = !₂[Real.cos (theta s), Real.sin (theta s)]

end DoCarmoDG


