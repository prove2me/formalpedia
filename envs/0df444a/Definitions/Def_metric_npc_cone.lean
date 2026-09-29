-- Prove2me | Definitions.Def_metric_npc_cone
-- name    : metric_npc_cone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T18:27:53.571926+00:00
-- url     : https://prove2.me/theorems/6de43962-9566-46a8-8b55-544dcd5e2c0f
-- title:
--   Metric midpoints, the CN inequality, and metric cones
-- statement:
--   Mathlib has no notion of a *metric* midpoint, no curvature condition on a metric space, and no metric cone. This file supplies the three, together with the local-geodesic condition needed to measure the length of a closed curve of constant speed.
--
--   **Metric midpoints.** In a bare metric space, $m$ is a midpoint of $x$ and $y$ when
--
--   $$
--   d(x,m)=d(m,y)=\tfrac12 d(x,y).
--   $$
--
--   Unlike the `midpoint` of a module, this is a relation rather than an operation: it need not exist and need not be unique. Existence for all pairs is recorded separately.
--
--   **Nonpositive curvature.** The condition used is the CN inequality of Bruhat and Tits: for every midpoint $m$ of $x$ and $y$ and every $z$,
--
--   $$
--   d(m,z)^2 \;\le\; \tfrac12 d(x,z)^2+\tfrac12 d(y,z)^2-\tfrac14 d(x,y)^2 .
--   $$
--
--   This is the standard synthetic formulation of nonpositive curvature. In Euclidean space it holds with equality, by the parallelogram law, so the inequality says that the space is no more spread out than Euclidean space along midpoints. Together with existence of midpoints and completeness it is the usual definition of an $\mathrm{NPC}$, or $\mathrm{CAT}(0)$, space, and it is the property under which harmonic map theory into metric targets is developed.
--
--   **Metric cones.** A cone structure on $X$ is a distinguished vertex together with a dilation action of the nonnegative reals scaling all distances by the factor applied:
--
--   $$
--   d(\lambda p,\lambda q)=\lambda\, d(p,q),\qquad 1\cdot p=p,\qquad 0\cdot p=\mathsf O,\qquad a\cdot(b\cdot p)=(ab)\cdot p .
--   $$
--
--   Tangent cones of nonpositively curved spaces carry this structure, and it is what gives meaning to homogeneity of a map of a given order.
--
--   **Local geodesics.** A curve $c:\mathbb{R}\to X$ is a local geodesic of speed $k$ at scale $\delta$ when $d(c(s),c(t))=k|s-t|$ whenever $|s-t|\le\delta$. The condition has to be local: a closed curve satisfies it and fails the corresponding global identity, since its endpoints coincide while the elapsed parameter does not vanish.
-- source:
--   Standard synthetic metric geometry. The CN inequality is due to F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2. See also M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren 319, Chapter II.1 (CAT(0) spaces) and Chapter I.5 (metric cones). Mathlib contains none of these notions: it has midpoint only in a module, and no curvature condition, metric cone or local geodesic.

import Mathlib

/-!
# Metric midpoints, nonpositive curvature, and metric cones

Mathlib has no notion of a *metric* midpoint (only `midpoint` in a module),
no CAT(0) or nonpositive-curvature condition, and no metric cone.  This file
supplies the three, together with the local-geodesic condition that appears
whenever one measures the length of a closed curve of constant speed.

The curvature condition used is the CN inequality of Bruhat and Tits, which
is the standard synthetic formulation: it says that the squared distance to a
fixed point is, along a midpoint, at most what it would be in Euclidean space,
where the inequality is an equality by the parallelogram law.
-/

namespace MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

/-- `m` is a metric midpoint of `x` and `y`: it is equidistant from both at
half their distance.  Unlike `midpoint`, this makes sense in a bare metric
space, where it need neither exist nor be unique. -/
def IsMidpoint (m x y : X) : Prop :=
  dist x m = dist x y / 2 ∧ dist m y = dist x y / 2

/-- Every pair of points has a midpoint. -/
def HasMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∃ m : X, IsMidpoint m x y

/-- The CN inequality of Bruhat and Tits: nonpositive curvature in the
synthetic sense.  Together with the existence of midpoints and completeness
this is the usual definition of an NPC, or CAT(0), space. -/
def IsNPC (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y m z : X, IsMidpoint m x y →
    dist m z ^ 2 ≤ dist x z ^ 2 / 2 + dist y z ^ 2 / 2 - dist x y ^ 2 / 4

/-- A metric cone structure: a distinguished vertex together with the dilation
action of the nonnegative reals, scaling all distances by the factor applied. -/
structure ConeStructure (X : Type*) [PseudoMetricSpace X] where
  vertex : X
  scale : ℝ → X → X
  scale_dist : ∀ lam : ℝ, 0 ≤ lam → ∀ p q : X,
    dist (scale lam p) (scale lam q) = lam * dist p q
  scale_one : ∀ p : X, scale 1 p = p
  scale_zero : ∀ p : X, scale 0 p = vertex
  scale_mul : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ p : X,
    scale a (scale b p) = scale (a * b) p

/-- A curve that is a geodesic of constant speed `k` at scales below `delta`.
The condition is deliberately local: a closed curve satisfies it and fails the
corresponding global identity, since its endpoints coincide. -/
def IsLocalGeodesicWithSpeed (c : ℝ → X) (k delta : ℝ) : Prop :=
  0 < delta ∧ ∀ s t : ℝ, |s - t| ≤ delta → dist (c s) (c t) = k * |s - t|

end MetricGeometry


