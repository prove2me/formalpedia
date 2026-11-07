-- Prove2me | Definitions.Def_PolygonPack_placedUV
-- name    : PolygonPack_placedUV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:25.603855+00:00
-- url     : https://prove2.me/theorems/3477b307-2264-4261-8b16-e95d0ec9f344
-- title:
--   Vertical sections and the vertical span of a placed polygon
-- statement:
--   Let $K$ be a placed polygon in diagonal coordinates. Its **vertical section** at abscissa $u$ is the interval $[f(u),g(u)]$ of the $v$-coordinates of its points above $u$, and $w(u)=g(u)-f(u)$. Its **bottom** is $\min_K v$, and its **vertical span** is $\max_K v-\min_K v$. The paper works on the central interval $I=[-1/4,1/4]$.
--
--   The central section $w(0)$ compares the room a polygon needs across different placements.
--
--   **Formalization Note** On an empty section these definitions give a junk value. Every use is at a point of $I$ in a chosen-diagonal placement of a polygon with diameter above one, where the diameter crosses the section.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.2, p.22

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_diag

namespace PolygonPack

/-- **Sections and vertical extent.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.2, p.22: "For a polygon in a chosen-diagonal placement,
let [f(u), g(u)] denote its vertical section at abscissa u, and write w(u) = g(u) − f(u)."

`placedUV v T` is the placed polygon in `(u, v)` coordinates. `secLo K u`, `secHi K u`, `wSec K u` are
`f(u)`, `g(u)`, `w(u)`. `vBottom K`, `vTop K`, `vSpan K` are the bottom coordinate `min_P v`, the top, and
the vertical span. `centralI` is `I = [−1/4, 1/4]`.

**Formalization Note.** An empty section gives a junk `sInf`, `sSup`. Every use lies on `I` or at `u = 0`
with a chosen-diagonal placement of diameter above one, where the diameter crosses the section. -/
noncomputable def placedUV (v : List (ℚ × ℚ)) (T : Pose) : Set (ℝ × ℝ) := diag '' placed v T

/-- The lower end `f(u)` of the vertical section. -/
noncomputable def secLo (K : Set (ℝ × ℝ)) (u : ℝ) : ℝ := sInf {y | (u, y) ∈ K}

/-- The upper end `g(u)` of the vertical section. -/
noncomputable def secHi (K : Set (ℝ × ℝ)) (u : ℝ) : ℝ := sSup {y | (u, y) ∈ K}

/-- The section length `w(u) = g(u) − f(u)`. -/
noncomputable def wSec (K : Set (ℝ × ℝ)) (u : ℝ) : ℝ := secHi K u - secLo K u

/-- The bottom coordinate `min_P v`. -/
noncomputable def vBottom (K : Set (ℝ × ℝ)) : ℝ := sInf (Prod.snd '' K)

/-- The top coordinate `max_P v`. -/
noncomputable def vTop (K : Set (ℝ × ℝ)) : ℝ := sSup (Prod.snd '' K)

/-- The vertical span. -/
noncomputable def vSpan (K : Set (ℝ × ℝ)) : ℝ := vTop K - vBottom K

/-- The interval `I = [−1/4, 1/4]`. -/
def centralI : Set ℝ := Set.Icc (-(1 / 4)) (1 / 4)

/-- `F` has Lipschitz constant at most `C` on `J`. -/
def IsLipOn (C : ℝ) (F : ℝ → ℝ) (J : Set ℝ) : Prop := ∀ x ∈ J, ∀ y ∈ J, |F x - F y| ≤ C * |x - y|

end PolygonPack


