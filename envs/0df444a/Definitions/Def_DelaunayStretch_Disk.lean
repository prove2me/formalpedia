-- Prove2me | Definitions.Def_DelaunayStretch_Disk
-- name    : DelaunayStretch_Disk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:25.050876+00:00
-- url     : https://prove2.me/theorems/8eb82374-a8be-4450-bb58-978771f769e8
-- title:
--   Closed disks, their upper and lower arcs, arc order and arc lengths
-- statement:
--   A **closed disk** $O$ in the plane is given by its center $o$ and its radius $r$; its boundary circle is $\partial O=\{p:\|p-o\|=r\}$. Points $z$ of the plane have coordinates $x(z)$ and $y(z)$.
--
--   When $\partial O$ meets the $x$-axis in two points, that is $|y(o)|<r$, these points are $w_-(O)$ and $w_+(O)$, with $x(w_\pm(O))=x(o)\pm\sqrt{r^2-y(o)^2}$. The **upper arc** of $O$ is the arc of $\partial O$ from $w_-(O)$ to $w_+(O)$ in the half-plane $\{y\ge 0\}$, the **lower arc** the one in $\{y\le0\}$. Both arcs are oriented from $w_-(O)$ to $w_+(O)$, which orders their points.
--
--   Write a point of $\partial O$ as $p=o+r\,e(t)$ with $e(t)=(\cos t,\sin t)$. On the upper arc the angle $t$ is taken in $(-\pi/2,3\pi/2]$ and decreases from $w_-(O)$ to $w_+(O)$; on the lower arc it is taken in $(\pi/2,5\pi/2]$ and increases. So $p$ does not come after $q$ on the upper arc when $t(q)\le t(p)$, and the part of the upper arc from $p$ to $q$ has length $r\,(t(p)-t(q))$; on the lower arc the inequalities and differences are reversed. Finally, for $y(a)>0>y(b)$, $c=a+\frac{y(a)}{y(a)-y(b)}(b-a)$ is the point where the $x$-axis crosses $[a,b]$, and $\mathrm{clip}_h(t)=\max(-h,\min(h,t))$.
--
--   These are the elementary objects of the disk-chain model: arc lengths are the weights of the ladder graph and enter the costs of all moves.
--
--   **Formalization Note** The plane is $\mathbb C$ ($x=\mathrm{re}$, $y=\mathrm{im}$). A disk is a pair (center, radius); positivity of the radius is assumed wherever the paper assumes it. The angle parameters are $\pi/2+\arg((p-o)(-i))$ and $3\pi/2+\arg((p-o)i)$. On the upper arc $t\in[-\gamma,\pi+\gamma]$ with $\sin\gamma=y(o)/r$, $|\gamma|<\pi/2$, so the parameter never wraps; arc lengths may exceed $\pi r$. For a chord of length $0$, a point $a=b$ on the $x$-axis, the crossing formula returns $a$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), §2, notation before Definition 2.1, p.12; clip, §3.1, p.15

import Mathlib

namespace DelaunayStretch

open Complex

/-- A **closed disk** `O` in the plane, given by its center `o = O.center` and radius
`r = O.radius`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), §2, notation
before Definition 2.1, p.12.

**Formalization Note** The plane `ℝ²` is identified with `ℂ`: a point `z` has coordinates
`x(z) = z.re` and `y(z) = z.im`, and the Euclidean norm `‖·‖` is the complex absolute value,
so `dist z w = ‖z − w‖`. The disk itself is the set `Metric.closedBall center radius`; only its
boundary circle `∂O` is used. Positivity of the radius is not part of the structure; every
statement that needs `r > 0` says so, as the paper does. -/
structure Disk where
  /-- the center `o` -/
  center : ℂ
  /-- the radius `r` -/
  radius : ℝ

namespace Disk

/-- The boundary circle `∂O` of the closed disk `O` (p.12). -/
def boundary (O : Disk) : Set ℂ := Metric.sphere O.center O.radius

/-- `∂O` meets the `x`-axis in two points, i.e. `|y(o)| < r` (p.12). -/
def MeetsAxisTwice (O : Disk) : Prop := |O.center.im| < O.radius

/-- Half the length of the chord of `∂O` on the `x`-axis, `√(r² − y(o)²)`. -/
noncomputable def axisHalfChord (O : Disk) : ℝ := Real.sqrt (O.radius ^ 2 - O.center.im ^ 2)

/-- The left point `w₋(O)` of `∂O` on the `x`-axis (p.12). Meaningful when
`O.MeetsAxisTwice`. -/
noncomputable def wMinus (O : Disk) : ℂ := ⟨O.center.re - O.axisHalfChord, 0⟩

/-- The right point `w₊(O)` of `∂O` on the `x`-axis (p.12). Meaningful when
`O.MeetsAxisTwice`. -/
noncomputable def wPlus (O : Disk) : ℂ := ⟨O.center.re + O.axisHalfChord, 0⟩

/-- The **upper arc** of `O`: the arc of `∂O` from `w₋(O)` to `w₊(O)` in `{y ≥ 0}` (p.12). -/
def upperArc (O : Disk) : Set ℂ := {p | p ∈ O.boundary ∧ 0 ≤ p.im}

/-- The **lower arc** of `O`: the arc of `∂O` from `w₋(O)` to `w₊(O)` in `{y ≤ 0}` (p.12). -/
def lowerArc (O : Disk) : Set ℂ := {p | p ∈ O.boundary ∧ p.im ≤ 0}

/-- The angle parameter of a point `p` of the upper arc: the `t` with `p = o + r e(t)`,
`e(t) = (cos t, sin t)`, taken in `(−π/2, 3π/2]`.

**Formalization Note** On the upper arc, `t ∈ [−γ, π + γ]` with `sin γ = y(o)/r` and
`|γ| < π/2` (the proof of Lemma 4.2, p.23), so `t` never wraps around; the upper arc is
traversed from `w₋(O)` (`t = π + γ`) to `w₊(O)` (`t = −γ`) with `t` decreasing. -/
noncomputable def upperAngle (O : Disk) (p : ℂ) : ℝ :=
  Real.pi / 2 + Complex.arg ((p - O.center) * (-I))

/-- The angle parameter of a point `p` of the lower arc: the `t` with `p = o + r e(t)`, taken
in `(π/2, 5π/2]`.

**Formalization Note** On the lower arc, `t ∈ [π + γ, 2π − γ]` (p.23); it is traversed from
`w₋(O)` (`t = π + γ`) to `w₊(O)` (`t = 2π − γ`) with `t` increasing. -/
noncomputable def lowerAngle (O : Disk) (p : ℂ) : ℝ :=
  3 * Real.pi / 2 + Complex.arg ((p - O.center) * I)

/-- On the upper arc of `O` (oriented from `w₋(O)` to `w₊(O)`), the point `p` does not come
after `q` (p.12). Meaningful for `p, q` on the upper arc. -/
def UpperNotAfter (O : Disk) (p q : ℂ) : Prop := O.upperAngle q ≤ O.upperAngle p

/-- On the lower arc of `O` (oriented from `w₋(O)` to `w₊(O)`), the point `p` does not come
after `q` (p.12). Meaningful for `p, q` on the lower arc. -/
def LowerNotAfter (O : Disk) (p q : ℂ) : Prop := O.lowerAngle p ≤ O.lowerAngle q

/-- The length of the part of the upper arc of `O` from `p` to `q`, `r · (t(p) − t(q))`.
Meaningful for `p, q` on the upper arc with `p` not after `q`; it may exceed `π r`, since the
upper arc has central angle `π + 2γ`. -/
noncomputable def upperArcLength (O : Disk) (p q : ℂ) : ℝ :=
  O.radius * (O.upperAngle p - O.upperAngle q)

/-- The length of the part of the lower arc of `O` from `p` to `q`, `r · (t(q) − t(p))`.
Meaningful for `p, q` on the lower arc with `p` not after `q`. -/
noncomputable def lowerArcLength (O : Disk) (p q : ℂ) : ℝ :=
  O.radius * (O.lowerAngle q - O.lowerAngle p)

end Disk

/-- The point where the `x`-axis crosses the segment `[a, b]`, for `y(a) > 0 > y(b)`:
`a + (y(a)/(y(a) − y(b))) (b − a)`. For a "chord of length 0", `a = b` on the `x`-axis
(Definition 3.5, p.17), the formula returns `a` itself (Lean's `x / 0 = 0`). -/
noncomputable def axisCrossing (a b : ℂ) : ℂ :=
  a + ((a.im / (a.im - b.im) : ℝ) : ℂ) * (b - a)

/-- The clipping `clip_h(t) = max(−h, min(h, t))` of `t` to `[−h, h]`, for `h ≥ 0` (§3.1,
p.15). -/
noncomputable def clip (h t : ℝ) : ℝ := max (-h) (min h t)

end DelaunayStretch


