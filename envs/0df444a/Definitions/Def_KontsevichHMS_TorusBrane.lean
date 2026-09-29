-- Prove2me | Definitions.Def_KontsevichHMS_TorusBrane
-- name    : KontsevichHMS_TorusBrane
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T02:50:51.470818+00:00
-- url     : https://prove2.me/theorems/c31ff435-1720-4185-84f7-c6d3f8766d41
-- title:
--   Graded branes on the flat two-torus and Kontsevich's triangle counts
-- statement:
--   This file sets up the A-side data of the last section of Kontsevich's address, *Two-dimensional tori: a return*.
--
--   The symplectic manifold is the flat torus $\Sigma = \mathbb{R}^2/\mathbb{Z}^2$, with the translation-invariant area form normalised by a parameter $\mathrm{area} > 0$: a region of Euclidean area $a$ has symplectic area $\mathrm{area} \cdot a$.
--
--   A **brane** is a closed geodesic equipped with a grading and a flat unitary line bundle. Concretely it consists of a primitive vector $v \in \mathbb{Z}^2$ and a point $c \in \mathbb{R}^2$, determining the geodesic $L = \{c + tv \bmod \mathbb{Z}^2\}$; a real number $\alpha$, the **grading**, constrained so that $(\cos \pi\alpha, \sin \pi\alpha)$ is a nonzero real multiple of $v$, i.e. a real lift of the direction angle divided by $\pi$; and a real constant $\theta$, the flat connection, whose parallel transport along a path of parameter length $s$ is $\exp(2\pi i\,\theta s)$.
--
--   Two branes are **transverse** when $\det(v_1,v_2) \neq 0$. The set $L_{b_1} \cap L_{b_2}$ of intersection points indexes a basis of the Floer space $\mathrm{Hom}(b_1,b_2)$, which is concentrated in the **Maslov degree** $\mu(b_1,b_2) = \lceil \alpha_2 - \alpha_1 \rceil$.
--
--   Given three branes and intersection points $p \in L_1 \cap L_2$, $q \in L_2 \cap L_3$ and $r \in L_1 \cap L_3$, a **triangle** is a triple $(P,Q,R)$ of lifts of $(p,q,r)$ to the universal cover with $PQ$ along a lift of $L_2$, $QR$ along a lift of $L_3$ and $RP$ along a lift of $L_1$, positively oriented; the vertex $P$ is normalised to lie in $[0,1)^2$, which selects exactly one representative of each $\mathbb{Z}^2$-translation class. Kontsevich's structure constant is the sum of the weights of all such triangles,
--
--   $$c(p,q,r) \;=\; \sum_{\text{triangles}} \exp\bigl(-\mathrm{area}\cdot \tfrac12\det(Q-P,\,R-P)\bigr) \cdot \exp\Bigl(2\pi i\bigl(\theta_2 s_2 + \theta_3 s_3 + \theta_1 s_1\bigr)\Bigr),$$
--
--   where $s_2, s_3, s_1$ are the parameter lengths of the three sides; it is the coefficient of $r$ in the product $m_2(p,q)$.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, pp. 18-19, section 'Two-dimensional tori: a return'

import Mathlib

/-!
# Graded Lagrangian branes on the flat two-torus, and Kontsevich's triangle counts

This file sets up the data appearing in the last section ("Two-dimensional tori: a return")
of M. Kontsevich, *Homological algebra of mirror symmetry*, ICM 1994 (alg-geom/9411018),
pp. 18-19.

The symplectic manifold is the standard flat torus `Σ = ℝ²/ℤ²` with the area form scaled so
that the total area is `area > 0`.  Objects of Fukaya's category (enlarged by unitary local
systems) are closed geodesics carrying a flat unitary line bundle; a geodesic carries in
addition a grading, i.e. a real lift of the direction angle, which produces the Maslov
grading on morphism spaces.

Morphisms between two transverse branes are spanned by the intersection points, and
Kontsevich's composition `m₂` is the sum over triangles in the universal cover `ℝ²` with
sides on the three geodesics, each weighted by `exp(-area of the triangle)` and by the
holonomies of the local systems along its sides.
-/

namespace KontsevichHMS

open scoped Real

/-- The flat two-torus `ℝ²/ℤ²`. -/
abbrev Torus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The universal covering projection `ℝ² → ℝ²/ℤ²`. -/
def proj (x : ℝ × ℝ) : Torus := ((x.1 : AddCircle (1 : ℝ)), (x.2 : AddCircle (1 : ℝ)))

/-- The determinant of two plane vectors; `det2 x y` is twice the signed area of the
triangle `0, x, y`. -/
def det2 (x y : ℝ × ℝ) : ℝ := x.1 * y.2 - x.2 * y.1

/-- A graded Lagrangian brane on the flat torus: a closed geodesic through `base` with
primitive integral direction `dir`, a grading `grading` (a real lift of the direction angle,
normalised so that the angle is `π * grading`), and a flat unitary line bundle whose
holonomy around a loop of parameter length `s` is `exp (2πi * conn * s)`. -/
structure Brane where
  /-- The primitive integral direction vector of the geodesic. -/
  dir : ℤ × ℤ
  /-- The direction vector is primitive. -/
  dir_primitive : IsCoprime dir.1 dir.2
  /-- A point the geodesic passes through. -/
  base : ℝ × ℝ
  /-- The grading: a real number whose angle `π * grading` points along `dir`. -/
  grading : ℝ
  /-- The grading is a lift of the direction angle. -/
  grading_dir : ∃ t : ℝ, t ≠ 0 ∧
    (Real.cos (π * grading), Real.sin (π * grading)) = t • ((dir.1 : ℝ), (dir.2 : ℝ))
  /-- The flat unitary connection on the line bundle, as a real constant. -/
  conn : ℝ

namespace Brane

/-- The direction vector of a brane, as a real vector. -/
def dirR (b : Brane) : ℝ × ℝ := ((b.dir.1 : ℝ), (b.dir.2 : ℝ))

/-- The preimage in `ℝ²` of the geodesic of `b`: the union of all its lifts. -/
def liftLine (b : Brane) : Set (ℝ × ℝ) :=
  {x | ∃ (t : ℝ) (g : ℤ × ℤ), x = b.base + t • b.dirR + ((g.1 : ℝ), (g.2 : ℝ))}

/-- The closed geodesic of `b`, as a subset of the torus. -/
def line (b : Brane) : Set Torus := proj '' b.liftLine

/-- Two branes are transverse when their directions are not parallel. -/
def Transverse (b₁ b₂ : Brane) : Prop := det2 b₁.dirR b₂.dirR ≠ 0

/-- The (finite, for transverse branes) set of intersection points of two branes; it indexes
a basis of the Floer complex `Hom(b₁, b₂)`. -/
def isect (b₁ b₂ : Brane) : Set Torus := b₁.line ∩ b₂.line

/-- The Maslov index of an intersection of two graded branes on a surface: `⌈α₂ - α₁⌉`,
where `αᵢ` are the gradings.  It is the degree in which the Floer complex
`Hom(b₁, b₂)` is concentrated. -/
noncomputable def maslov (b₁ b₂ : Brane) : ℤ := ⌈b₂.grading - b₁.grading⌉

/-- The parameter length of a displacement `w` along the direction of `b`: the real number
`s` with `w = s • dirR b` when `w` is parallel to `dirR b`. -/
noncomputable def param (b : Brane) (w : ℝ × ℝ) : ℝ :=
  (w.1 * b.dirR.1 + w.2 * b.dirR.2) / (b.dirR.1 ^ 2 + b.dirR.2 ^ 2)

end Brane

open Brane

/-- The set of holomorphic triangles contributing to the coefficient of `r` in the product
`m₂(p, q)`, where `p ∈ b₁ ∩ b₂`, `q ∈ b₂ ∩ b₃` and `r ∈ b₁ ∩ b₃`.

A triangle is a triple of vertices `(P, Q, R)` in the universal cover lifting `(p, q, r)`,
with the side `PQ` on a lift of `b₂`, the side `QR` on a lift of `b₃` and the side `RP` on a
lift of `b₁`, and positively oriented.  Translating by `ℤ²` acts freely on such triples, and
the normalisation `P ∈ [0,1) × [0,1)` picks exactly one representative of each orbit. -/
def triangles (b₁ b₂ b₃ : Brane) (p q r : Torus) :
    Set ((ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) :=
  {T | proj T.1 = p ∧ T.1.1 ∈ Set.Ico (0 : ℝ) 1 ∧ T.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      proj T.2.1 = q ∧ proj T.2.2 = r ∧
      det2 (T.2.1 - T.1) b₂.dirR = 0 ∧
      det2 (T.2.2 - T.2.1) b₃.dirR = 0 ∧
      det2 (T.1 - T.2.2) b₁.dirR = 0 ∧
      0 < det2 (T.2.1 - T.1) (T.2.2 - T.1)}

/-- The weight of a triangle: `exp (- symplectic area)` times the holonomies of the three
flat line bundles along the three sides. -/
noncomputable def triangleWeight (area : ℝ) (b₁ b₂ b₃ : Brane)
    (T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Complex.exp (-(area * det2 (T.2.1 - T.1) (T.2.2 - T.1) / 2 : ℝ)) *
    Complex.exp (2 * π * Complex.I *
      ((b₂.conn * param b₂ (T.2.1 - T.1) + b₃.conn * param b₃ (T.2.2 - T.2.1)
        + b₁.conn * param b₁ (T.1 - T.2.2) : ℝ)))

/-- Kontsevich's structure constant: the coefficient of the intersection point `r` in the
composition `m₂(p, q)` of the intersection points `p ∈ b₁ ∩ b₂` and `q ∈ b₂ ∩ b₃`, on the
torus of total area `area`.  It is the sum of the weights of all contributing triangles. -/
noncomputable def mTwoCoeff (area : ℝ) (b₁ b₂ b₃ : Brane) (p q r : Torus) : ℂ :=
  ∑' T : ↥(triangles b₁ b₂ b₃ p q r), triangleWeight area b₁ b₂ b₃ T.1

end KontsevichHMS


