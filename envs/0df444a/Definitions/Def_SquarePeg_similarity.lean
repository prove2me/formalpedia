-- Prove2me | Definitions.Def_SquarePeg_similarity
-- name    : SquarePeg_similarity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T23:19:03.573835+00:00
-- url     : https://prove2.me/theorems/137e1364-a4f9-44a9-8226-3667d1d6364a
-- title:
--   Rotations, orientation-preserving similarities, cyclic quadrilaterals
-- statement:
--   $\mathrm{rot}(\theta)$ is counterclockwise rotation of the plane through angle $\theta$. $\mathrm{opSim}(s,\theta,t)(x)=t+s\,\mathrm{rot}(\theta)(x)$ is an orientation-preserving similarity (positive scale $s$, rotation $\theta$, translation $t$). $\mathrm{IsCyclicQuadrilateral}(q_1,q_2,q_3,q_4)$ holds when the four points are pairwise distinct and lie on a common circle of positive radius; this is Greene-Lobb's notion of a cyclic quadrilateral (one that inscribes in a circle).
-- source:
--   Greene-Lobb, Cyclic quadrilaterals and smooth Jordan curves, arXiv:2011.05216, definitions of 'inscribes' and 'cyclic' (Introduction).

import Mathlib
import Definitions.Def_SchoenfliesPlaneCore

open Schoenflies

namespace SquarePeg

/-- Counterclockwise rotation of the plane through angle θ. -/
noncomputable def rot (θ : ℝ) (x : Plane) : Plane :=
  Plane.mk (Real.cos θ * x 0 - Real.sin θ * x 1) (Real.sin θ * x 0 + Real.cos θ * x 1)

/-- An orientation-preserving similarity: positive scale s, rotation θ, translation t. -/
noncomputable def opSim (s : ℝ) (θ : ℝ) (t : Plane) (x : Plane) : Plane :=
  t + s • rot θ x

/-- A cyclic quadrilateral: four distinct points lying on a common circle. -/
def IsCyclicQuadrilateral (q1 q2 q3 q4 : Plane) : Prop :=
  q1 ≠ q2 ∧ q1 ≠ q3 ∧ q1 ≠ q4 ∧ q2 ≠ q3 ∧ q2 ≠ q4 ∧ q3 ≠ q4 ∧
  ∃ (c : Plane) (r : ℝ), 0 < r ∧
    ‖q1 - c‖ = r ∧ ‖q2 - c‖ = r ∧ ‖q3 - c‖ = r ∧ ‖q4 - c‖ = r

end SquarePeg


