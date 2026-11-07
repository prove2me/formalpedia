-- Prove2me | Definitions.Def_PolygonPack_IsCentralBottom
-- name    : PolygonPack_IsCentralBottom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:58:04.951227+00:00
-- url     : https://prove2.me/theorems/95e690d4-3861-4b27-b263-957278a6f0bd
-- title:
--   Extreme central sections, the retained length and the common diagonal
-- statement:
--   In a packing of a family $F$, a polygon has the **bottommost central section** if its section at $u=0$ lies below the section of every other polygon of $F$, and the **topmost** one likewise. The **retained length** $W$ is the sum of $w(0)$ over the polygons of $F$ other than the two extreme ones. So $W=0$ if $|F|\le2$. The family has a **common diagonal** if the fixed diameters all follow one diagonal, and it is **normalized** if they all follow the $u$-diagonal. A polygon has **latest start at most $t$** if it is Tight with $d\le t$, or Slack with $\delta/2-h\le t$.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.5, p.27

import Mathlib
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_IsTight

namespace PolygonPack

/-- Polygon `i` in the packing `T`, in `(u, v)` coordinates. -/
noncomputable def packedUV (I : Instance) (T : Fin I.n → Pose) (i : Fin I.n) : Set (ℝ × ℝ) :=
  placedUV (I.verts i) (T i)

/-- **Extreme central sections and the retained length.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.5, p.27: "Remove the bottommost and
topmost sections on u = 0, or remove all polygons if there are at most two. The remaining sections have total
length W".

`IsCentralBottom I T F b`: the central section of `b` lies below that of every other polygon of `F`.
`IsCentralTop` is the mirror image. `retainedW I T F b t` is `W` for the extreme polygons `b` and `t`.
`SameDiagonal` says that the fixed diameters in `F` all follow one diagonal, `IsNormalized` that they follow the
`u`-diagonal, and `JobBelow c a0 v t` that the polygon is Tight or Slack with its latest start `d` at most `t`
(`d = δ/2 − h` for Slack).

**Formalization Note.** If `|F| ≤ 2`, then `F \ {b, t}` is empty, so `W = 0`, as printed. -/
def IsCentralBottom (I : Instance) (T : Fin I.n → Pose) (F : Finset (Fin I.n)) (b : Fin I.n) : Prop :=
  b ∈ F ∧ ∀ i ∈ F, i ≠ b → secHi (packedUV I T b) 0 ≤ secLo (packedUV I T i) 0

/-- The central section of `t` lies above that of every other polygon of `F`. -/
def IsCentralTop (I : Instance) (T : Fin I.n → Pose) (F : Finset (Fin I.n)) (t : Fin I.n) : Prop :=
  t ∈ F ∧ ∀ i ∈ F, i ≠ t → secHi (packedUV I T i) 0 ≤ secLo (packedUV I T t) 0

/-- The total central length `W` after removing the two extreme polygons. -/
noncomputable def retainedW (I : Instance) (T : Fin I.n → Pose) (F : Finset (Fin I.n)) (b t : Fin I.n) : ℝ :=
  ∑ i ∈ F \ {b, t}, wSec (packedUV I T i) 0

/-- The placed fixed diameter of polygon `i` follows the `u`-diagonal. -/
def DiamFollowsU (I : Instance) (T : Fin I.n → Pose) (i : Fin I.n) : Prop :=
  FollowsU ((T i).act (castPt (diamPair (I.verts i)).1)) ((T i).act (castPt (diamPair (I.verts i)).2))

/-- The fixed diameters of `F` all follow one diagonal. -/
def SameDiagonal (I : Instance) (T : Fin I.n → Pose) (F : Finset (Fin I.n)) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, (DiamFollowsU I T i ↔ DiamFollowsU I T j)

/-- The fixed diameters of `F` all follow the `u`-diagonal. -/
def IsNormalized (I : Instance) (T : Fin I.n → Pose) (F : Finset (Fin I.n)) : Prop :=
  ∀ i ∈ F, DiamFollowsU I T i

/-- The polygon is Tight with canonical bottom at most `t`, or Slack with `δ/2 − h ≤ t`. -/
def JobBelow (c a0 : ℝ) (v : List (ℚ × ℚ)) (t : ℝ) : Prop :=
  (IsTight c a0 v ∧ canonD v ≤ t) ∨ (IsSlack c a0 v ∧ polyDelta v / 2 - polyH v ≤ t)

end PolygonPack


