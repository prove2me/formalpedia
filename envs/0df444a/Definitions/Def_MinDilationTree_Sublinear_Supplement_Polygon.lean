-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_Supplement_Polygon
-- name    : MinDilationTree_Sublinear_Supplement_Polygon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:53:25.341207+00:00
-- url     : https://prove2.me/theorems/edd8bd14-72ad-465d-b720-28d1d233cfec
-- title:
--   Weakly simple polygons, geodesic distance and thin regions
-- statement:
--   A **polygon** is given by a closed boundary walk $\partial P = w_0, w_1, \ldots, w_{m-1}, w_0$ of line segments in $\mathbb R^2$, with $m\ge1$. Repeated visits of the walk to a point count as distinct vertices, so a polygon may have degenerate one-dimensional parts, and a single point ($m=1$) is a polygon.
--
--   1. The **trace** of the walk is the union of its closed edges. The closed polygon $P$ is the trace together with every point off the trace around which the walk winds an odd number of times (computed by the horizontal-ray crossing rule). Its interior is $\operatorname{int}(P)=P\setminus\partial P$.
--   2. The walk is **weakly simple** when (i) for every $\varepsilon>0$ the vertices of an ordered subdivision of the walk (points inserted along its edges, in order) can be moved by less than $\varepsilon$ each so that they form a simple polygon, and (ii) the complement $\mathbb R^2\setminus P$ is path-connected.
--   3. The **longest edge** of the walk is $\max_i\|w_i-w_{i+1}\|$, indices modulo $m$.
--   4. For a set $P$, the **geodesic distance** $d_P(a,b)\in[0,\infty]$ is the infimum of the lengths of polygonal paths from $a$ to $b$ inside $P$ ($+\infty$ if there is none); $D_P(a,R)$ is the geodesic disk. The geodesic diameter of $X$ is at most $d$ when $d_X(x,y)\le d$ for all $x,y\in X$.
--   5. A set $P$ is **$\Lambda$-thin** when every closed disk contained in $P$ has radius at most $\Lambda$ (Definition 3).
--
--   These objects carry every statement of the supplement about supports, junction trees and obstructions.
--
--   **Formalization Note** Condition (ii) is footnote 1's restriction to polygons whose complement is path-connected; with the odd-winding region it excludes self-touching polygons that enclose a hole. The subdivision in (i) is what admits the singletons and doubly traversed segments the paper explicitly allows (a simple polygon needs at least three vertices). The plane is `EuclideanSpace ℝ (Fin 2)`; distances are in $[0,\infty]$.
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 3 (PDF p. 4), §2 "Polygons" and footnote 1; Definition 3; p. 6 (PDF p. 7), Lemma 4 (r = max edge)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_GeometricGraph

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- §2, p.3 (PDF 4): a polygon is given by a closed boundary walk of line segments.
Occurrences are indexed, so repeated visits of the walk to a point are distinct vertices.
The closing edge runs from occurrence `m - 1` back to occurrence `0`. -/
structure BoundaryWalk where
  m : ℕ
  positive : 0 < m
  vertex : Fin m → Plane

/-- Cyclic access to the occurrences of a boundary walk. -/
def BoundaryWalk.at (w : BoundaryWalk) (i : ℕ) : Plane :=
  w.vertex ⟨i % w.m, Nat.mod_lt _ w.positive⟩

/-- The boundary walk as a point set: the union of its closed edges (zero-length edges included). -/
def BoundaryWalk.trace (w : BoundaryWalk) : Set Plane :=
  {x | ∃ i : Fin w.m, x ∈ segment ℝ (w.at i) (w.at (i.val + 1))}

/-- Number of edges crossed by the horizontal ray from `x` to the right, with the usual half-open
rule at vertices (an edge counts when exactly one endpoint lies strictly above the line through
`x`). For `x` off the trace its parity is the winding number of the walk around `x` mod 2.
The division is only evaluated when the endpoints are on different sides of that line. -/
noncomputable def BoundaryWalk.rayCrossings (w : BoundaryWalk) (x : Plane) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin w.m =>
    let a := w.at i
    let b := w.at (i.val + 1)
    ((x 1 < a 1 ∧ b 1 ≤ x 1) ∨ (x 1 < b 1 ∧ a 1 ≤ x 1)) ∧
      x 0 < a 0 + (x 1 - a 1) / (b 1 - a 1) * (b 0 - a 0)).card

/-- The closed polygon `P` bounded by the walk: its trace together with the points off the trace
around which the walk winds an odd number of times. Degenerate one-dimensional parts belong to
the trace, hence to `P`. -/
noncomputable def BoundaryWalk.region (w : BoundaryWalk) : Set Plane :=
  w.trace ∪ {x | Odd (w.rayCrossings x)}

/-- `int(P) = P \ ∂P`, with `∂P` the trace of the walk (the boundary of the ε-perturbed polygon
in the limit; degenerate parts are boundary). -/
noncomputable def BoundaryWalk.interior (w : BoundaryWalk) : Set Plane :=
  w.region \ w.trace

/-- An ordinary simple polygon: at least three pairwise distinct vertices and edges that meet
only in shared endpoints. -/
def BoundaryWalk.IsSimple (w : BoundaryWalk) : Prop :=
  3 ≤ w.m ∧ Function.Injective w.vertex ∧
    ∀ i j : Fin w.m, i ≠ j →
      segment ℝ (w.at i) (w.at (i.val + 1)) ∩ segment ℝ (w.at j) (w.at (j.val + 1)) ⊆
        ({w.at i, w.at (i.val + 1)} ∩ {w.at j, w.at (j.val + 1)})

/-- `v` is an ordered subdivision of `w`: every edge of `w` is replaced by a monotone sequence of
points along it (repetitions allowed). This changes the representation of the walk, not its trace
or its traversal. -/
def BoundaryWalk.Subdivides (v w : BoundaryWalk) : Prop :=
  ∃ cut : ℕ → ℕ, cut 0 = 0 ∧ cut w.m = v.m ∧
    (∀ i, i < w.m → cut i < cut (i + 1)) ∧
    ∃ t : ℕ → ℝ,
      (∀ i, i < w.m → t (cut i) = 0) ∧
      (∀ i j, i < w.m → cut i ≤ j → j < cut (i + 1) →
        0 ≤ t j ∧ t j ≤ 1 ∧ v.at j = (1 - t j) • w.at i + t j • w.at (i + 1)) ∧
      (∀ i j k, i < w.m → cut i ≤ j → j ≤ k → k < cut (i + 1) → t j ≤ t k)

/-- §2, p.3 (PDF 4), and footnote 1: a weakly simple polygon. (i) For every `ε > 0` the vertices of
(an ordered subdivision of) the walk can be moved by less than `ε` to obtain a simple polygon, and
(ii) the complement of the closed polygon is path-connected. The subdivision admits the
degenerate polygons the paper explicitly allows (a single point, a doubly traversed segment), which
have fewer than three vertices; for a walk that is itself perturbable no subdivision is needed. -/
def BoundaryWalk.IsWeaklySimple (w : BoundaryWalk) : Prop :=
  IsPathConnected w.regionᶜ ∧
    ∀ ε : ℝ, 0 < ε → ∃ v q : BoundaryWalk,
      v.Subdivides w ∧ v.m = q.m ∧ q.IsSimple ∧
        ∀ i : ℕ, i < v.m → dist (v.at i) (q.at i) < ε

/-- Lemma 4's `r = maxᵢ ‖pᵢ - pᵢ₊₁‖`, indices modulo `m`. -/
noncomputable def BoundaryWalk.maxEdge (w : BoundaryWalk) : ℝ :=
  Finset.univ.sup' ⟨⟨0, w.positive⟩, Finset.mem_univ _⟩
    (fun i : Fin w.m => ‖w.at i.val - w.at (i.val + 1)‖)

/-- Geodesic distance `d_P(a, b)` in a closed region: the infimum of the lengths of polygonal paths
from `a` to `b` contained in `P`; `+∞` if there is none. -/
noncomputable def geodesic (P : Set Plane) (a b : Plane) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (v : Fin (k + 1) → Plane)
    (_ : v 0 = a) (_ : v (Fin.last k) = b)
    (_ : ∀ i : Fin (k + 1), v i ∈ P)
    (_ : ∀ i : Fin k, segment ℝ (v i.castSucc) (v i.succ) ⊆ P),
      ∑ i : Fin k, ENNReal.ofReal ‖v i.castSucc - v i.succ‖

/-- The geodesic disk `D_P(a, R)`. -/
noncomputable def geodesicDisk (P : Set Plane) (a : Plane) (R : ℝ) : Set Plane :=
  {x ∈ P | geodesic P a x ≤ ENNReal.ofReal R}

/-- The geodesic diameter of `X` (measured inside `X`) is at most `d`. -/
def GeodesicDiamLE (X : Set Plane) (d : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, geodesic X x y ≤ ENNReal.ofReal d

/-- Definition 3, p.3 (PDF 4): `P` is `Λ`-thin when every disk contained in `P` has radius at most
`Λ` (so the largest one does). -/
def RegionThin (P : Set Plane) (Λ : ℝ) : Prop :=
  ∀ (x : Plane) (R : ℝ), 0 ≤ R → Metric.closedBall x R ⊆ P → R ≤ Λ

end MinDilationTree.Sublinear.Supplement


