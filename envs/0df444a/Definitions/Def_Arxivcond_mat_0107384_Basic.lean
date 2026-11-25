-- Prove2me | Definitions.Def_Arxivcond_mat_0107384_Basic
-- name    : Arxivcond_mat_0107384_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T20:15:28.812333+00:00
-- url     : https://prove2.me/theorems/1319ea6d-d6e9-4672-a2d5-ec0ea34f8df4
-- title:
--   Regular polygons inscribed in a circle, the polygon radius of eq. (12) and the disk radius
-- statement:
--   Objects of Sec. 2 and Sec. 4 of Tuncer, *How round is round?* (2002).
--
--   1. **Plane.** The inclusion lies in the Euclidean plane $\mathbb{R}^2$ with the Euclidean distance. Area is two-dimensional Lebesgue measure, and the closed ball $\bar B(c,r)$ is the round disk of radius $r$ centred at $c$.
--   2. **Regular polygon (Sec. 4, Fig. 4, before eq. 12).** For $n\in\mathbb{N}$, a centre $c$, a radius $r$ and an orientation angle $\theta$, the vertices are
--   $$v_k=c+r\,(\cos(\theta+2\pi k/n),\ \sin(\theta+2\pi k/n)),\qquad k=0,\dots,n-1.$$
--   They lie on the circle of radius $r$ about $c$. The regular $n$-gon $P_n(c,r,\theta)$ is the closed convex hull of $v_0,\dots,v_{n-1}$, so $r$ is its circumradius.
--   3. **Polygon radius (eq. 12).** $r_n(q)=\sqrt{q/(n\sin(\pi/n)\cos(\pi/n))}$.
--   4. **Disk radius (Sec. 2, after eqs. 6-7).** $r(q)=\sqrt{q/\pi}$, the radius of the disk inclusion of area fraction $q$ in the unit cell of area $1$.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)`, not `ℝ × ℝ`: on `ℝ × ℝ` Mathlib's metric is the sup metric, and its closed balls are squares. The paper fixes neither the centre nor the orientation of the polygon, so both are parameters.
-- source:
--   Tuncer, How round is round? On accuracy in complex dielectric permittivity calculations: a finite-size scaling approach, arXiv:cond-mat/0107384v3 (2002), Sec. 2 after eqs. (6)-(7), PDF p. 4; Sec. 4, Fig. 4 and eq. (12), PDF p. 8

import Mathlib

/-!
Tuncer, *How round is round? On accuracy in complex dielectric permittivity calculations:
a finite-size scaling approach*, arXiv:cond-mat/0107384v3 (2002): the regular polygons with `n`
sides that replace the disk inclusion in Sec. 4 (Fig. 4, eq. (12)), the polygon radius `r_n` of
eq. (12), and the disk radius `r = √(q/π)` of Sec. 2.

The inclusion lives in the Euclidean plane, modelled as `EuclideanSpace ℝ (Fin 2)`, so that
`Metric.closedBall c r` is a round disk and `volume` is the area (two-dimensional Lebesgue
measure).
-/

open MeasureTheory

noncomputable section

namespace Arxivcond_mat_0107384

/-- Sec. 3, Fig. 2, and Sec. 4: the two-dimensional plane of the unit cell, with the Euclidean
distance and area. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Sec. 4, Fig. 4 and the sentence before eq. (12): the `k`-th vertex (`k = 0, …, n-1`) of the
regular polygon with `n` sides generated from the circle of radius `r` centred at `c`. The vertices
sit on that circle at the angles `θ + 2πk/n`; `θ` fixes the orientation of the polygon. -/
def polygonVertex (n : ℕ) (c : Plane) (r θ : ℝ) (k : Fin n) : Plane :=
  c + r • !₂[Real.cos (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / (n : ℝ)),
    Real.sin (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / (n : ℝ))]

/-- Sec. 4, Fig. 4 and the sentence before eq. (12): the (closed, filled) regular polygon with `n`
sides inscribed in the circle of radius `r` centred at `c`, i.e. the convex hull of its `n`
vertices. -/
def regularPolygon (n : ℕ) (c : Plane) (r θ : ℝ) : Set Plane :=
  convexHull ℝ (Set.range (polygonVertex n c r θ))

/-- Sec. 4, eq. (12): the radius `r_n = √(q / (n sin(π/n) cos(π/n)))` of the circle generating a
regular `n`-gon of area `q`. -/
def polygonRadius (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (q / ((n : ℝ) * Real.sin (Real.pi / n) * Real.cos (Real.pi / n)))

/-- Sec. 2, after eqs. (6)-(7): the radius `r = √(q/π)` of a disk of area `q` (the disk inclusion
of area fraction `q` in the unit cell). -/
def diskRadius (q : ℝ) : ℝ :=
  Real.sqrt (q / Real.pi)

end Arxivcond_mat_0107384


