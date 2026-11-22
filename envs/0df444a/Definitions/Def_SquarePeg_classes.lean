-- Prove2me | Definitions.Def_SquarePeg_classes
-- name    : SquarePeg_classes
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T23:18:46.922329+00:00
-- url     : https://prove2.me/theorems/0089778f-0e4d-4416-957f-2e9cc68cab6a
-- title:
--   Curve classes for the square peg problem
-- statement:
--   Regularity and symmetry classes of plane curves used in the partial results. $\mathrm{IsConvexCurve}(C)$: $C$ is the boundary of a compact convex set with non-empty interior. $\mathrm{IsSmoothCurve}(C)$: $C$ is the image of a regular $C^\infty$ 1-periodic parametrization injective on $[0,1)$ (a smooth embedded circle). $\mathrm{IsLocallyMonotone}(C)$: near each point some linear functional is injective on $C$ (Stromquist's condition, equivalently locally a graph over a line). $\mathrm{IsLineSymmetric}$ / $\mathrm{IsPointSymmetric}$: invariance under reflection in a line / point-reflection about a point.
-- source:
--   Convex: Emch, Amer. J. Math. 35 (1913) 407-412; Fenn, Bull. LMS 2 (1970) 73-76. Smooth: Greene-Lobb, arXiv:2005.09193 and arXiv:2011.05216. Locally monotone: Stromquist, Mathematika 36 (1989) 187-197, definition as in Matschke survey Theorem 2. Symmetric: Nielsen-Wright, Geom. Dedicata 56 (1995) 285-297.

import Mathlib
import Definitions.Def_SchoenfliesPlaneCore

open Schoenflies Set

namespace SquarePeg

/-- A convex curve: the boundary of a compact convex set with non-empty interior. -/
def IsConvexCurve (C : Set Plane) : Prop :=
  ∃ K : Set Plane, Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ C = frontier K

/-- A smooth Jordan curve: the image of a regular C^∞ 1-periodic parametrization
that is injective on [0,1). -/
def IsSmoothCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContDiff ℝ ⊤ f ∧ (∀ t, f (t + 1) = f t) ∧
    InjOn f (Ico 0 1) ∧ (∀ t, deriv f t ≠ 0) ∧ f '' Icc 0 1 = C

/-- Stromquist's locally monotone condition: near each of its points the curve is
injectively projected by some linear functional (locally a graph over a line). -/
def IsLocallyMonotone (C : Set Plane) : Prop :=
  ∀ p ∈ C, ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧
    ∃ ℓ : Plane →ₗ[ℝ] ℝ, InjOn ℓ (C ∩ U)

/-- Symmetric across some line (reflection invariance). -/
def IsLineSymmetric (C : Set Plane) : Prop :=
  ∃ a u : Plane, ‖u‖ = 1 ∧
    ∀ p ∈ C, a + ((2 * inner ℝ (p - a) u) • u - (p - a)) ∈ C

/-- Symmetric about some point (point-reflection invariance). -/
def IsPointSymmetric (C : Set Plane) : Prop :=
  ∃ z : Plane, ∀ p ∈ C, 2 • z - p ∈ C

end SquarePeg


