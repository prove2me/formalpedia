-- Prove2me | Definitions.Def_StackingStars_Main_Geometry
-- name    : StackingStars_Main_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:42:23.132458+00:00
-- url     : https://prove2.me/theorems/e85ca00a-6c90-4258-a561-88fcd0f41829
-- title:
--   Plane geometry: dot and cross products, Euclidean length, area, convex-hull area, spans, rectangles, vertical parallelograms
-- statement:
--   The plane is $\mathbb R\times\mathbb R$ (`Pt`), the carrier of the published `PolygonPack.Pose`. Because Mathlib's metric on $\mathbb R\times\mathbb R$ is the sup-metric, every Euclidean quantity is written out explicitly:
--
--   * `dot u v` $=u\cdot v=u_1v_1+u_2v_2$; `cross u v` $=u\times v=u_1v_2-u_2v_1$ (positive exactly when $v$ points to the left of $u$); `len u` $=\|u\|=\sqrt{u\cdot u}$.
--   * `rotCCW`, `rotCW`: rotation by $90^\circ$ counterclockwise, $(x,y)\mapsto(-y,x)$, and clockwise, $(x,y)\mapsto(y,-x)$.
--   * `area S` $=|S|$, the Lebesgue measure of $S$ as a real number; `hullArea S` $=|\operatorname{conv}S|$, the least area of a convex container of $S$.
--   * `spanIn z S` $=\operatorname{span}_z(S)=\sup_{x\in S}z\cdot x-\inf_{x\in S}z\cdot x$, the width of $S$ in the direction $z$ (used for nonempty bounded $S$ and unit $z$).
--   * `rect p f g a b` $=\{p+sf+tg: 0\le s\le a,\ 0\le t\le b\}$, a rectangle with side directions $f,g$ and side lengths $a,b$ when $f,g$ are orthonormal.
--   * `vertParallelogram x₀ x₁ s b₀ b₁` $=\{(x,y): x_0\le x\le x_1,\ sx+b_0\le y\le sx+b_1\}$, a parallelogram with two vertical sides.
--   * `ray q p` $=\{q+t(p-q):t\ge0\}$; `homothety q α S` $=q+\alpha(S-q)$; `translate t S` $=S+t$.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 3 (|·| is area), p. 13 (Lemma 9), p. 19 (span_z)

import Mathlib

namespace StackingStars.Main

/-!
# Plane geometry used throughout

Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, *Stacking Stars: Minimum-Area Packing with and
without Rotation*, STOC 2027 submission (manuscript sha256 ee9554eb…), §1–3. The plane is
`ℝ × ℝ` (the carrier of the published `PolygonPack.Pose`). Mathlib's metric on `ℝ × ℝ` is the
sup-metric, so every Euclidean length, dot product and distance below is written out explicitly.
`|S|` (area) is the Lebesgue measure `volume` on `ℝ × ℝ`, as a real number.
-/

/-- A point (or vector) of the plane. -/
abbrev Pt := ℝ × ℝ

/-- Euclidean dot product `u · v`. -/
def dot (u v : Pt) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The cross product (determinant) `u × v = u₁v₂ − u₂v₁`; it is positive exactly when `v` points
to the left of `u`. -/
def cross (u v : Pt) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Euclidean length `‖u‖`. -/
noncomputable def len (u : Pt) : ℝ := Real.sqrt (dot u u)

/-- Rotation by 90° counterclockwise: `(x, y) ↦ (−y, x)`. -/
def rotCCW (u : Pt) : Pt := (-u.2, u.1)

/-- Rotation by 90° clockwise: `(x, y) ↦ (y, −x)`. -/
def rotCW (u : Pt) : Pt := (u.2, -u.1)

/-- The area `|S|` of a set: its Lebesgue measure as a real number. -/
noncomputable def area (S : Set Pt) : ℝ := (MeasureTheory.volume S).toReal

/-- The area of the convex hull of `S`: the least area of a convex container of `S`. -/
noncomputable def hullArea (S : Set Pt) : ℝ := area (convexHull ℝ S)

/-- `span_z(S)`: the width of `S` in the direction `z`, `sup_{x∈S} z·x − inf_{x∈S} z·x`
(used for nonempty bounded `S` and unit `z`). -/
noncomputable def spanIn (z : Pt) (S : Set Pt) : ℝ :=
  sSup ((fun x => dot z x) '' S) - sInf ((fun x => dot z x) '' S)

/-- The rectangle with corner `p`, side directions `f`, `g` and side lengths `a`, `b`:
`{p + s f + t g : 0 ≤ s ≤ a, 0 ≤ t ≤ b}` (a rectangle when `f`, `g` are orthonormal). -/
def rect (p f g : Pt) (a b : ℝ) : Set Pt :=
  {x | ∃ s ∈ Set.Icc (0 : ℝ) a, ∃ t ∈ Set.Icc (0 : ℝ) b, x = p + s • f + t • g}

/-- The vertical parallelogram `{(x, y) : x₀ ≤ x ≤ x₁, s x + b₀ ≤ y ≤ s x + b₁}`: two vertical
sides on `x = x₀`, `x = x₁` and two parallel sides of slope `s`. -/
def vertParallelogram (x₀ x₁ s b₀ b₁ : ℝ) : Set Pt :=
  {z | x₀ ≤ z.1 ∧ z.1 ≤ x₁ ∧ s * z.1 + b₀ ≤ z.2 ∧ z.2 ≤ s * z.1 + b₁}

/-- The closed ray from `q` through `p`: `{q + t (p − q) : t ≥ 0}`. -/
def ray (q p : Pt) : Set Pt := {x | ∃ t : ℝ, 0 ≤ t ∧ x = q + t • (p - q)}

/-- The homothetic copy `q + α (S − q)` of `S` with center `q` and ratio `α`. -/
def homothety (q : Pt) (α : ℝ) (S : Set Pt) : Set Pt := (fun z => q + α • (z - q)) '' S

/-- The translate `S + t`. -/
def translate (t : Pt) (S : Set Pt) : Set Pt := (fun z => z + t) '' S

end StackingStars.Main


