-- Prove2me | Definitions.Def_graphene_lattice
-- name    : graphene_lattice
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T20:07:00.994978+00:00
-- url     : https://prove2.me/theorems/97f4a45e-3836-4ddd-b2a5-9b49f14b1dc7
-- title:
--   Honeycomb lattice geometry of graphene
-- statement:
--   The geometric data of graphene's honeycomb lattice, in the notation of Eq. (1) of the
--   source. Points and wave vectors of the plane are elements of $\mathbb{R}\times\mathbb{R}$,
--   written $p=(p_1,p_2)$.
--
--   - $p\cdot q = p_1q_1+p_2q_2$;
--   - $\lVert q\rVert_2=\sqrt{q_1^2+q_2^2}$ — introduced explicitly because the product type
--     $\mathbb{R}\times\mathbb{R}$ carries the sup norm, not the Euclidean one;
--   - lattice unit vectors $a_1=\tfrac{a}{2}(3,\sqrt3)$, $a_2=\tfrac{a}{2}(3,-\sqrt3)$;
--   - nearest-neighbour vectors $\delta_1=\tfrac{a}{2}(1,\sqrt3)$,
--     $\delta_2=\tfrac{a}{2}(1,-\sqrt3)$, $\delta_3=-a(1,0)$, collected as a family indexed by
--     a three-element type;
--   - the Dirac points $K=\frac{2\pi}{3\sqrt3 a}(\sqrt3,1)$ and
--     $K'=\frac{2\pi}{3\sqrt3 a}(\sqrt3,-1)$, stored in the equivalent component form
--     $K=\bigl(\frac{2\pi}{3a},\frac{2\pi}{3\sqrt3 a}\bigr)$,
--     $K'=\bigl(\frac{2\pi}{3a},-\frac{2\pi}{3\sqrt3 a}\bigr)$.
--
--   Here $a$ is the carbon–carbon distance, taken positive in the theorems that need it; the
--   definitions themselves place no restriction on $a$.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Mathlib

/-!
# Graphene: honeycomb lattice geometry

Geometric data of the honeycomb lattice of graphene, following
F. Utermohlen, *Tight-Binding Model for Graphene* (September 12, 2018), Eq. (1).

Positions and momenta are elements of `ℝ × ℝ`.  Note that the norm carried by the
product type `ℝ × ℝ` is the sup norm, so the Euclidean norm is introduced here
explicitly as `euclidNorm`.
-/

namespace GrapheneTightBinding

/-- Euclidean inner product of two vectors of the plane `ℝ × ℝ`. -/
def dotp (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- The Euclidean norm `√(q₁² + q₂²)` of a vector of the plane `ℝ × ℝ`.
(The product type `ℝ × ℝ` carries the sup norm, hence this explicit definition.) -/
noncomputable def euclidNorm (q : ℝ × ℝ) : ℝ := Real.sqrt (q.1 ^ 2 + q.2 ^ 2)

/-- The first lattice unit vector `a₁ = (a/2)(3, √3)`. -/
noncomputable def latticeVecOne (a : ℝ) : ℝ × ℝ := (3 * a / 2, Real.sqrt 3 * a / 2)

/-- The second lattice unit vector `a₂ = (a/2)(3, -√3)`. -/
noncomputable def latticeVecTwo (a : ℝ) : ℝ × ℝ := (3 * a / 2, -(Real.sqrt 3 * a / 2))

/-- The three nearest-neighbour vectors
`δ₁ = (a/2)(1, √3)`, `δ₂ = (a/2)(1, -√3)`, `δ₃ = -a(1, 0)`. -/
noncomputable def nnVec (a : ℝ) : Fin 3 → ℝ × ℝ
  | 0 => (a / 2, Real.sqrt 3 * a / 2)
  | 1 => (a / 2, -(Real.sqrt 3 * a / 2))
  | 2 => (-a, 0)

/-- The Dirac point `K = (2π/(3√3 a))(√3, 1)`. -/
noncomputable def diracK (a : ℝ) : ℝ × ℝ :=
  (2 * Real.pi / (3 * a), 2 * Real.pi / (3 * Real.sqrt 3 * a))

/-- The Dirac point `K' = (2π/(3√3 a))(√3, -1)`. -/
noncomputable def diracKp (a : ℝ) : ℝ × ℝ :=
  (2 * Real.pi / (3 * a), -(2 * Real.pi / (3 * Real.sqrt 3 * a)))

end GrapheneTightBinding


