-- Prove2me | Definitions.Def_SubdetDiameter_Polytope_sphericalCone
-- name    : SubdetDiameter_Polytope_sphericalCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:04:00.992284+00:00
-- url     : https://prove2.me/theorems/4d6c666b-7e64-4bed-b6db-ae9031c4cebe
-- title:
--   Spherical cones, dockable surface, cones of revolution
-- statement:
--   Geometric vocabulary of §2 of Bonifas et al. (2014), in $\mathbb{R}^n$ with the closed unit ball $B_n = \{x : \|x\|_2 \le 1\}$.
--
--   1. **Spherical cone.** A (not necessarily convex) cone is a set $C \subseteq \mathbb{R}^n$ closed under multiplication by non-negative scalars. A spherical cone is a set of the form $S = C \cap B_n$ with $C$ a cone.
--   2. **Dockable surface.** The dockable surface $D(S)$ of a spherical cone $S$ is the $(n-1)$-dimensional volume of the part of the boundary of $S$ that is not on the unit sphere:
--   $$D(S) := \mathcal H^{n-1}\big(\partial S \cap \operatorname{int} B_n\big),$$
--   where $\mathcal H^{n-1}$ is the $(n-1)$-dimensional Hausdorff measure normalised to agree with Lebesgue measure on hyperplanes.
--   3. **Cone of revolution.** For a vector $v \ne 0$ and an angle $\theta$, the spherical cone of revolution with axis $v$ and angle $\theta$ is the set of vectors of the unit ball forming an angle of at most $\theta$ with $v$:
--   $$S = \Big\{x \in B_n : \frac{v^T x}{\|v\|\,\|x\|} \ge \cos\theta\Big\}.$$
--
--   These are the objects of the isoperimetric step of the paper: the ratio $D(S)/\mathrm{vol}(S)$ is bounded above for the spherical cones $C_v \cap B_n$ of a polytope and below for all spherical cones of at most half the ball's volume.
--
--   **Formalization Note** $D(S)$ uses Mathlib's `μHE[n-1]` (`euclideanHausdorffMeasure`), not the raw `μH[n-1]`, which differs by a dimensional constant; it is applied to `frontier S ∩ Metric.ball 0 1`. The cone of revolution is written without division, $\{x \in B_n : \cos\theta\,\|v\|\,\|x\| \le \langle v, x\rangle\}$, so it contains the apex $0$ as a cone must. The angle restriction $0 < \theta \le \pi/2$ and $v \ne 0$ are hypotheses of the theorems that use it. Natural-number subtraction makes the dimension $n-1$ equal to $0$ at $n = 0$, where $\mathbb{R}^0$ is a point and every statement about spherical cones is trivial.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 106 (cone, spherical cone), p. 107 (dockable surface D(S)), p. 109 (cone of revolution)

import Mathlib

open scoped RealInnerProductSpace

namespace SubdetDiameter.Polytope

/-- A **spherical cone** in `ℝ^n`: the intersection of a (not necessarily convex) cone
`C` — a set closed under multiplication by non-negative scalars — with the closed unit
ball `B_n`. -/
def IsSphericalCone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ C : Set (EuclideanSpace ℝ (Fin n)),
    (∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C) ∧ S = C ∩ Metric.closedBall 0 1

/-- The **dockable surface** `D(S)` of a spherical cone `S ⊆ ℝ^n`: the
`(n-1)`-dimensional (Euclidean-normalised Hausdorff) measure of the part of the boundary
of `S` that is not on the unit sphere, i.e. of `∂S ∩ int B_n`. -/
noncomputable def dockable {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ENNReal :=
  MeasureTheory.Measure.euclideanHausdorffMeasure (n - 1) (frontier S ∩ Metric.ball 0 1)

/-- The **spherical cone of revolution** with axis `v` and angle `θ`: the vectors of the
unit ball forming an angle of at most `θ` with `v`,
`{x ∈ B_n : vᵀx ≥ cos θ · ‖v‖ ‖x‖}` (the apex `0` included). -/
def coneOfRevolution {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ Metric.closedBall 0 1 ∧ Real.cos θ * (‖v‖ * ‖x‖) ≤ ⟪v, x⟫}

end SubdetDiameter.Polytope


