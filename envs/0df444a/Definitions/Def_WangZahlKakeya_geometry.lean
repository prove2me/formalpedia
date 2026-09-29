-- Prove2me | Definitions.Def_WangZahlKakeya_geometry
-- name    : WangZahlKakeya_geometry
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T05:09:39.197392+00:00
-- url     : https://prove2.me/theorems/7ac7d7c6-f730-4841-87fc-3c28c02014d1
-- title:
--   Tubes, prisms, slabs, Kakeya sets and box-counting dimension in $\mathbb{R}^3$
-- statement:
--   This file fixes the geometric vocabulary of the mission inside $\mathbb{R}^3$, realized as the three-dimensional Euclidean space $E_3$ with its usual metric and Lebesgue measure.
--
--   For $p, w \in E_3$ and $\delta \in \mathbb{R}$, the **tube** $T(p, w, \delta)$ is the closed $\delta$-neighbourhood of the line segment joining $p$ to $p + w$:
--
--   $$T(p,w,\delta) \;=\; \bigcup_{0 \le t \le 1} \overline{B}\big(p + t\,w,\ \delta\big).$$
--
--   When $\|w\| = 1$ this is a $\delta$-tube in the sense of Wang–Zahl: the $\delta$-neighbourhood of a unit line segment. Its **$2$-fold dilate** is the tube with the same centre, twice the radius and twice the length, namely $T\big(p - \tfrac12 w,\ 2w,\ 2\delta\big)$. The symbol $|T|$ of the paper is realized as the volume of the reference tube $T(0, e_1, \delta)$; every $\delta$-tube is an isometric copy of it, so this is the common volume of a $\delta$-tube.
--
--   A **rectangular prism** with centre $p$, orthonormal frame $u_0, u_1, u_2$ and side lengths $d_0, d_1, d_2$ is
--
--   $$\Big\{x \in E_3 : |\langle x - p, u_i\rangle| \le d_i/2 \text{ for } i = 0,1,2\Big\},$$
--
--   and a set is a prism of dimensions $d$ when it can be written this way for some centre and some orthonormal frame. A **slab** is the intersection of the closed unit ball with the closed $t$-neighbourhood of an affine plane $\{x : \langle x, u\rangle = c\}$, where $u$ is a unit normal and $t \ge 0$.
--
--   A **Kakeya set** is a compact $K \subseteq E_3$ such that for every unit vector $v$ there is a point $x$ with $\{x + t v : 0 \le t \le 1\} \subseteq K$, i.e. $K$ contains a unit line segment in every direction.
--
--   Finally, for a set $A$ and a radius $r > 0$ the **covering number** $N(A, r)$ is the least $m$ for which $A$ can be covered by $m$ open balls of radius $r$, and the **upper** and **lower Minkowski (box-counting) dimensions** of $A$ are
--
--   $$\overline{\dim}_{\mathrm M} A = \limsup_{r \to 0^+} \frac{\log N(A,r)}{\log(1/r)}, \qquad \underline{\dim}_{\mathrm M} A = \liminf_{r \to 0^+} \frac{\log N(A,r)}{\log(1/r)} .$$
--
--   These notions are the substrate for every statement in the mission: the goal theorem is phrased with Kakeya sets and the two Minkowski dimensions, while the volume estimates are phrased with tubes, prisms and slabs.
--
--   **Formalization Note** Mathlib supplies Hausdorff dimension but no box-counting dimension, so the covering number and both Minkowski dimensions are defined here. The covering number is an infimum over natural numbers, hence equals $0$ when no finite cover exists; this only affects unbounded sets, and Kakeya sets are compact. The inner product is written out in coordinates as $\sum_i x_i y_i$ so that prisms and slabs are defined without reference to any particular inner-product API.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, §1 (Theorem 1.1), §1.2, §3.1 (Definitions 3.1--3.6) and §1.6 (Conjecture 1.11)

import Mathlib

/-!
# Geometry for the Wang–Zahl Kakeya mission

Basic geometric objects used in Wang–Zahl, *Volume estimates for unions of convex sets,
and the Kakeya set conjecture in three dimensions* (arXiv:2502.17655v1):
`δ`-tubes, prisms, slabs, Kakeya sets, and the box-counting (Minkowski) dimensions.
-/

namespace WangZahlKakeya

open MeasureTheory Metric Set

/-- Euclidean three–dimensional space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The standard inner product of two vectors of `E3`, written out in coordinates. -/
noncomputable def dot (x y : E3) : ℝ := ∑ i, x i * y i

/-- The `δ`-tube with base point `p` and direction vector `w`: the closed `δ`-neighbourhood
of the line segment from `p` to `p + w`. When `‖w‖ = 1` this is the `δ`-neighbourhood of a
unit line segment, i.e. a `δ`-tube in the sense of the paper. -/
def tube (p w : E3) (δ : ℝ) : Set E3 := ⋃ t ∈ Set.Icc (0 : ℝ) 1, closedBall (p + t • w) δ

/-- The `2`-fold dilate of the `δ`-tube `tube p w δ`: the tube with the same centre,
twice the radius and twice the length. -/
def tubeDilate2 (p w : E3) (δ : ℝ) : Set E3 := tube (p - (2⁻¹ : ℝ) • w) ((2 : ℝ) • w) (2 * δ)

/-- The common volume `|T|` of a `δ`-tube, computed on a reference tube.  Every `δ`-tube is
an isometric copy of this one, so this is the quantity denoted `|T|` in the paper. -/
noncomputable def tubeVol (δ : ℝ) : ℝ :=
  (volume (tube 0 (EuclideanSpace.single 0 (1 : ℝ)) δ)).toReal

/-- A rectangular prism with centre `p`, orthonormal frame `u` and side lengths `d`. -/
def prism (p : E3) (u : Fin 3 → E3) (d : Fin 3 → ℝ) : Set E3 :=
  {x : E3 | ∀ i, |dot (x - p) (u i)| ≤ d i / 2}

/-- `W` is a rectangular prism with side lengths `d 0`, `d 1`, `d 2`. -/
def IsPrismOfDims (W : Set E3) (d : Fin 3 → ℝ) : Prop :=
  ∃ p : E3, ∃ u : Fin 3 → E3,
    (∀ i j, dot (u i) (u j) = if i = j then 1 else 0) ∧ W = prism p u d

/-- A *slab*: the intersection of the unit ball with the closed `t`-neighbourhood of an
affine plane `{x : dot x n = c}`, where `n` is a unit normal vector. -/
def IsSlab (W : Set E3) : Prop :=
  ∃ (u : E3) (c t : ℝ), ‖u‖ = 1 ∧ 0 ≤ t ∧
    W = closedBall (0 : E3) 1 ∩ {x : E3 | |dot x u - c| ≤ t}

/-- A *Kakeya set* in `ℝ³`: a compact set containing a unit line segment in every direction. -/
def IsKakeyaSet (K : Set E3) : Prop :=
  IsCompact K ∧ ∀ v : E3, ‖v‖ = 1 → ∃ x : E3, (fun t : ℝ => x + t • v) '' Set.Icc (0 : ℝ) 1 ⊆ K

/-- The `r`-covering number of `A`: the least number of open balls of radius `r` needed to
cover `A` (`0` if no finite cover exists, by the convention `sInf ∅ = 0` on `ℕ`). -/
noncomputable def coveringNumber (A : Set E3) (r : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ c : Fin m → E3, A ⊆ ⋃ i, ball (c i) r}

/-- The upper Minkowski (upper box-counting) dimension of `A`, i.e.
`limsup_{r → 0⁺} log N(A, r) / log (1/r)`, where `N(A, r)` is the `r`-covering number. -/
noncomputable def upperMinkowskiDim (A : Set E3) : ℝ :=
  Filter.limsup (fun r : ℝ => Real.log (coveringNumber A r) / Real.log (1 / r))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The lower Minkowski (lower box-counting) dimension of `A`, i.e.
`liminf_{r → 0⁺} log N(A, r) / log (1/r)`, where `N(A, r)` is the `r`-covering number. -/
noncomputable def lowerMinkowskiDim (A : Set E3) : ℝ :=
  Filter.liminf (fun r : ℝ => Real.log (coveringNumber A r) / Real.log (1 / r))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

end WangZahlKakeya


