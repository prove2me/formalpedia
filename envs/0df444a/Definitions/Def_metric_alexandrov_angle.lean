-- Prove2me | Definitions.Def_metric_alexandrov_angle
-- name    : metric_alexandrov_angle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T22:48:17.090361+00:00
-- url     : https://prove2.me/theorems/fc42c7fe-7994-4de8-861d-43ec83f27266
-- title:
--   Geodesic lines and the Alexandrov angle
-- statement:
--   Mathlib has no geodesic line in a metric space and no angle between curves — only `InnerProductGeometry.angle` between two vectors of an inner product space. This file supplies both, on top of the comparison angle.
--
--   **Geodesic lines.** A geodesic line is a curve $\gamma:\mathbb R\to X$ parametrized by arclength globally:
--
--   $$
--   d\bigl(\gamma(s),\gamma(t)\bigr)=|s-t|\qquad\text{for all }s,t\in\mathbb R .
--   $$
--
--   Unlike a geodesic segment this is a complete, unbounded geodesic; its two halves issuing from $\gamma(0)$ are the model of a pair of opposite directions.
--
--   **The Alexandrov angle.** Given two curves $g_1,g_2$ issuing from a point $p$, the Alexandrov (or upper) angle between them is
--
--   $$
--   \angle_p(g_1,g_2)\;=\;\limsup_{s,t\to 0^+}\ \widetilde\angle_p\bigl(g_1(s),g_2(t)\bigr),
--   $$
--
--   the limit superior of the Euclidean comparison angles subtended by points on the two curves as both parameters tend to $0$ from above. The limit superior is taken along the product of the two punctured neighbourhood filters $\mathcal N_{>0}(0)\times\mathcal N_{>0}(0)$, which is the standard way of saying "as $s\to0^+$ and $t\to0^+$ independently".
--
--   The limit superior, rather than the limit, is what makes the definition unconditional: it exists in every metric space, whereas the genuine limit exists only under a curvature bound (in a CAT($\kappa$) space the comparison angle is monotone in $s$ and $t$, so the limsup is a limit). Since comparison angles lie in $[0,\pi]$, so does the Alexandrov angle, in any metric space whatsoever.
--
--   This is the metric replacement for the angle between two tangent vectors, and it is the object the space of directions at a point is built from: the directions at $p$ are the equivalence classes of geodesics issuing from $p$ under "Alexandrov angle zero", and the Alexandrov angle descends to a metric on that quotient. For a Euclidean building, the resulting space of directions at each point is the spherical building that governs the local structure — which is exactly what a harmonic map into such a building must be compared against.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren 319, Chapter I.1 (geodesic lines) and Definition II.3.1 / II.3.18 (the Alexandrov angle and the space of directions). Mathlib has no geodesic line in a metric space and no angle between curves.

import Mathlib
import Definitions.Def_metric_geodesic_angle

/-!
# Geodesic lines and the Alexandrov angle

The Alexandrov, or upper, angle between two geodesics issuing from a common
point is the limit superior of the comparison angles subtended by points on
them as both approach the vertex.  It is the metric replacement for the angle
between two tangent vectors, and it is what the space of directions at a point
is built from.

Mathlib has neither geodesic lines in a metric space nor any angle between
curves; only the angle between two vectors of an inner product space.
-/

namespace MetricGeometry

open Filter Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- A complete geodesic line, parametrized by arclength. -/
def IsGeodesicLine (gamma : ℝ → X) : Prop :=
  ∀ s t : ℝ, dist (gamma s) (gamma t) = |s - t|

/-- The Alexandrov (upper) angle at `p` between two curves issuing from it:
the limit superior of the comparison angles as both parameters tend to `0`
from above. -/
noncomputable def alexandrovAngle (p : X) (g1 g2 : ℝ → X) : ℝ :=
  Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2))
    ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))

end MetricGeometry


