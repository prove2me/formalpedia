-- Prove2me | Definitions.Def_IrrationalTriangleBilliard
-- name    : IrrationalTriangleBilliard
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.571783+00:00
-- url     : https://prove2.me/theorems/b0d95053-57d2-4121-b9d1-67e09a129f04
-- statement:
--   A triangle is given by three affinely independent complex numbers (vertices in the Euclidean plane). Its table is the open interior of the convex hull; side i is the open segment from vertex i to vertex i+1 (indices mod 3), with tangent vertex(i+1) minus vertex(i), and angle(i) is the interior angle at vertex i; HasIrrationalAngle says some angle is an irrational multiple of π. The reflection of a velocity v in the line spanned by tangent e is (e/ē)·v̄, preserving the tangential and reversing the normal component. Phase space is ℂ × Circle (position and unit direction). A FlightChain for a triangle and phase z is a complete two-sided billiard trajectory through z: strictly increasing collision times indexed by ℤ, unbounded in both directions, with time 0 strictly before 0 and time 1 strictly after 0, collision points lying in open sides (never vertices), straight constant-speed flight between consecutive collisions staying inside the open table, z recovered by flying back from collision 0 along direction 0, and the outgoing direction at each collision equal to the specular reflection of the previous direction in that side's tangent. FlightChain.at gives the state at time t (using outgoing velocity at collisions), and billiardFlow Q t z follows the chain from z if one exists and otherwise leaves z fixed. The phase measure is normalized area on the open table times uniform probability measure on the circle. MainConclusion(Q) is a defined proposition, not an established theorem, asserting that the phase measure has total mass 1; almost every phase has a chain; chains are unique for every z; each billiardFlow Q t preserves the phase measure; billiardFlow Q (s+t) agrees almost everywhere with the composition of flows at s and t for all real s,t; and every measurable set invariant modulo null sets under every flow time has measure 0 or 1, i.e. the flow is ergodic.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IrrationalTriangleBilliard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IrrationalTriangleBilliard.lean; bytes 16..4882
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
The phase space is represented in the ambient plane × circle, with measure
supported on the interior of the triangle. Values on side-collision states
at a fixed time are immaterial to the modulo-null-set conclusion. The
trajectories themselves include the collisions and impose specular reflection.
-/

open MeasureTheory Set
open scoped ENNReal symmDiff

noncomputable section

namespace TriangularBilliards

/-- Three affinely independent vertices in the Euclidean plane. -/
structure Triangle where
  vertex : Fin 3 → ℂ
  nondegenerate : AffineIndependent ℝ vertex

namespace Triangle

/-- The open table; the complex plane carries its ordinary real Euclidean metric. -/
def table (Q : Triangle) : Set ℂ := interior (convexHull ℝ (range Q.vertex))

/-- The open side from vertex `i` to the next vertex, indexed cyclically. -/
def side (Q : Triangle) (i : Fin 3) : Set ℂ :=
  openSegment ℝ (Q.vertex i) (Q.vertex (i + 1))

/-- A tangent vector to side `i`, with no choice of inward or outward normal. -/
def tangent (Q : Triangle) (i : Fin 3) : ℂ := Q.vertex (i + 1) - Q.vertex i

/-- Interior angle at vertex `i`. -/
def angle (Q : Triangle) (i : Fin 3) : ℝ :=
  InnerProductGeometry.angle (Q.vertex (i + 1) - Q.vertex i)
    (Q.vertex (i + 2) - Q.vertex i)

def HasIrrationalAngle (Q : Triangle) : Prop :=
  ∃ i : Fin 3, Irrational (Q.angle i / Real.pi)

end Triangle

/-- Reflection in the real line spanned by the nonzero tangent `e`.
In coordinates with `e` real this is complex conjugation, preserving the
tangential component and reversing the normal component. -/
def reflect (e v : ℂ) : ℂ := (e / star e) * star v

instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle

instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

abbrev Phase := ℂ × Circle

/-- A complete nonsingular billiard trajectory, indexed by its collisions.
Flight zero contains the initial time strictly. Both ends of the collision
time sequence are unbounded; collisions occur only in open sides, never
vertices. These are geometric conditions, not ergodicity/analytic assumptions. -/
structure FlightChain (Q : Triangle) (z : Phase) where
  time : ℤ → ℝ
  point : ℤ → ℂ
  direction : ℤ → Circle
  wall : ℤ → Fin 3
  increasing : StrictMono time
  unbounded_below : ∀ t : ℝ, ∃ n : ℤ, time n < t
  unbounded_above : ∀ t : ℝ, ∃ n : ℤ, t < time n
  zero_before : time 0 < 0
  zero_after : 0 < time 1
  on_side : ∀ n : ℤ, point n ∈ Q.side (wall n)
  flight : ∀ n : ℤ,
    point (n + 1) = point n + (time (n + 1) - time n) • (direction n : ℂ)
  inside : ∀ (n : ℤ) (t : ℝ), time n < t → t < time (n + 1) →
    point n + (t - time n) • (direction n : ℂ) ∈ Q.table
  start_point : z.1 = point 0 + (-time 0) • (direction 0 : ℂ)
  start_direction : z.2 = direction 0
  specular : ∀ n : ℤ,
    (direction n : ℂ) = reflect (Q.tangent (wall n)) (direction (n - 1) : ℂ)

/-- The geometric state on a chain, using outgoing velocity at a collision. -/
def FlightChain.at {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) : Phase := by
  classical
  exact if h : ∃ n : ℤ, c.time n ≤ t ∧ t < c.time (n + 1) then
    let n := Classical.choose h
    (c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n)
  else z

/-- The actual specular flow on complete regular chains. Singular initial
states are assigned their initial state; the theorem must prove these form
a null set. No nonemptiness of the regular set is postulated. -/
def billiardFlow (Q : Triangle) (t : ℝ) (z : Phase) : Phase := by
  classical
  exact if h : Nonempty (FlightChain Q z) then (Classical.choice h).at t else z

/-- Uniform angular probability, parameterized by [0,2π). -/
def angularMeasure : Measure Circle :=
  Measure.map Circle.exp
    ((ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ico 0 (2 * Real.pi)))

/-- Exactly normalized area in the open table times uniform angular measure. -/
def phaseMeasure (Q : Triangle) : Measure Phase :=
  ((volume Q.table)⁻¹ • volume.restrict Q.table).prod angularMeasure

/-- The main conclusion, together with the geometric/nonvacuity guarantees
needed by the concrete definition of the actual two-sided billiard. -/

def MainConclusion (Q : Triangle) : Prop :=
  phaseMeasure Q univ = 1 ∧
  (∀ᵐ z ∂phaseMeasure Q, Nonempty (FlightChain Q z)) ∧
  (∀ (z : Phase) (c d : FlightChain Q z), c = d) ∧
  (∀ t : ℝ, MeasurePreserving (billiardFlow Q t) (phaseMeasure Q) (phaseMeasure Q)) ∧
  (∀ s t : ℝ, billiardFlow Q (s + t) =ᵐ[phaseMeasure Q]
    (billiardFlow Q s ∘ billiardFlow Q t)) ∧
  (∀ A : Set Phase, MeasurableSet A →
    (∀ t : ℝ, phaseMeasure Q (((billiardFlow Q t) ⁻¹' A) ∆ A) = 0) →
    phaseMeasure Q A = 0 ∨ phaseMeasure Q A = 1)



end TriangularBilliards
end
end OAI


