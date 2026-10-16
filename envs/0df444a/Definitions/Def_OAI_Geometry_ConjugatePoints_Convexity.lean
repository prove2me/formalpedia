-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
-- name    : OAI_Geometry_ConjugatePoints_Convexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:13:38.899978+00:00
-- url     : https://prove2.me/theorems/ec6b67f4-24ab-4980-83af-797a2e474138
-- title:
--   Midpoint maps with the CN inequality, minsets of isometries, and translation coordinates along geodesic lines
-- statement:
--   This file introduces the metric-space notions used to obstruct nonpositively curved metrics through the action of the fundamental group: midpoint maps satisfying the CN inequality, convex sets, minimal displacement sets, nearest-point coordinates on geodesic lines, and concatenations of translates of a path.
--
--   Let $(X, d)$ be a metric space.
--
--   1. **CN midpoint structure.** A CN midpoint structure on $X$ is a map $m : X \times X \to X$ such that for all $x, y, z \in X$
--   $$
--   d\big(m(x, y), z\big)^2 \le \frac{d(x, z)^2 + d(y, z)^2}{2} - \frac{d(x, y)^2}{4}.
--   $$
--
--   2. **Midpoint-convex sets.** A set $S \subseteq X$ is midpoint convex (for $m$) if $m(x, y) \in S$ whenever $x, y \in S$.
--
--   3. **Halving sequence.** For $p, q \in X$: $q_0 = q$ and $q_{n+1} = m(p, q_n)$.
--
--   4. **Minset.** For a map $f : X \to X$, $\operatorname{Min}(f) = \{x \in X : d(x, f(x)) \le d(y, f(y)) \text{ for all } y \in X\}$, the set where the displacement $x \mapsto d(x, f(x))$ attains its minimum (possibly empty).
--
--   5. **Nearest points.** If $X$ is proper, every nonempty closed set $S$ contains a point $p$ with $d(x, p) \le d(x, z)$ for all $z \in S$. For an isometric embedding $c : \mathbb{R} \to X$ (a geodesic line) and $x \in X$ there is $r \in \mathbb{R}$ with $d(x, c(r)) \le d(x, c(s))$ for all $s$; the line coordinate $\tau_c(x)$ is a chosen such $r$.
--
--   6. **Axis shift.** For a proper $X$, a geodesic line $c$ and an isometry $g$ of $X$, the shift of $g$ along $c$ is $\tau_c(g(c(0)))$, the line coordinate of the image of the base point $c(0)$.
--
--   7. **Axis join.** For an isometry $f$ of $X$ and a path $q : \mathbb{R} \to X$, the joined curve is
--   $$
--   t \mapsto f^{\lfloor t \rfloor}\big(q(t - \lfloor t \rfloor)\big),
--   $$
--   which concatenates the translates $f^n \circ q|_{[0,1)}$, $n \in \mathbb{Z}$.
--
--   These objects are the vocabulary for the later analysis of commuting isometries of a CN space: projections onto convex sets, translation lengths along axes, and the resulting obstruction for isometries satisfying commutator relations.
--
--   **Formalization Note** The structure is `NonpositiveMetric.CNMidpoint X` with fields `mid` and `cn`; `MidConvex`, `halfSequence`, `minset`, `lineCoordinate`, `axisShift`, `axisJoin` are defined in its namespace. Isometries of $X$ are `X ≃ᵢ X` with integer powers `f ^ Int.floor t`; the line coordinate is selected with `Classical.choose` and is not claimed to be unique. Several sections only open variables and are empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Convexity.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Convexity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance

namespace OAI

noncomputable section

/-!
# Midpoint convexity, minsets, and the semisimple shear obstruction.
-/

section
open Set Filter Topology
namespace ThreeManifold.NonpositiveMetric
variable (X : Type*) [MetricSpace X]

structure CNMidpoint where
  mid : X → X → X
  cn : ∀ x y z, dist (mid x y) z ^2 ≤
    (dist x z ^2 + dist y z ^2)/2 - dist x y ^2/4
namespace CNMidpoint
variable {X} (C : CNMidpoint X)
include C

end CNMidpoint
end ThreeManifold.NonpositiveMetric
end

section
open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

def MidConvex (S : Set X) : Prop := ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → C.mid x y ∈ S

def halfSequence (C : CNMidpoint X) (p q : X) : ℕ → X
  | 0 => q
  | n+1 => C.mid p (halfSequence C p q n)

include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

def minset (f : X → X) : Set X := {x | ∀ y, dist x (f x) ≤ dist y (f y)}

lemma exists_projection [ProperSpace X] {S : Set X} (hc : IsClosed S) (hne : S.Nonempty)
    (x : X) : ∃ p ∈ S, ∀ z ∈ S, dist x p ≤ dist x z := by
  obtain ⟨p,hp,he⟩ := hc.exists_infDist_eq_dist hne x
  refine ⟨p,hp,?_⟩
  intro z hz
  rw [← he]
  exact Metric.infDist_le_dist_of_mem hz

include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C
omit C in
lemma exists_line_coordinate [ProperSpace X] (c : ℝ → X) (hc : Isometry c) (x : X) :
    ∃ r : ℝ, ∀ s : ℝ, dist x (c r) ≤ dist x (c s) := by
  obtain ⟨p,⟨r,rfl⟩,hm⟩ := exists_projection hc.isClosedEmbedding.isClosed_range
    (range_nonempty c) x
  exact ⟨r,fun s => hm _ (mem_range_self s)⟩

omit C in
def lineCoordinate [ProperSpace X] (c : ℝ → X) (hc : Isometry c) (x : X) : ℝ :=
  (exists_line_coordinate c hc x).choose

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C
end

section
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)

def axisShift (c : ℝ → X) (hc : Isometry c) (g : X ≃ᵢ X) : ℝ :=
  lineCoordinate c hc (g (c 0))

include C
end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C
omit C in
def axisJoin (f : X ≃ᵢ X) (q : ℝ → X) (t : ℝ) : X := (f ^ Int.floor t) (q (Int.fract t))

end

variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint
end

open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint

end

end OAI


