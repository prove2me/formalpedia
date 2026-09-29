-- Prove2me | Definitions.Def_Larmor_vec3
-- name    : Larmor_vec3
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T01:01:33.294396+00:00
-- url     : https://prove2.me/theorems/b4216f47-3674-4a2a-a735-acadcf4e1628
-- title:
--   Vector calculus in $\mathbb{R}^3$: cross product, divergence, curl
-- statement:
--   This file fixes the three-dimensional arena in which the whole development takes place.
--
--   Points and vectors live in $V=\mathbb{R}^3$ equipped with its standard Euclidean inner product $\langle u,v\rangle=\sum_{i} u_i v_i$ and the associated norm. Three operations are introduced.
--
--   1. The **cross product** of $u,v\in V$ is
--   $$u\times v=\bigl(u_1v_2-u_2v_1,\; u_2v_0-u_0v_2,\; u_0v_1-u_1v_0\bigr),$$
--   components being indexed by $0,1,2$.
--
--   2. For a vector field $F:V\to V$, a direction index $j$ and a component index $i$, the **partial derivative** $\partial_j F_i(x)$ is the $i$-th component of the derivative of $F$ at $x$ in the $j$-th coordinate direction.
--
--   3. From these, the **divergence** and the **curl** of a vector field are
--   $$\nabla\cdot F=\sum_{i}\partial_i F_i,\qquad
--   \nabla\times F=\bigl(\partial_1F_2-\partial_2F_1,\;\partial_2F_0-\partial_0F_2,\;\partial_0F_1-\partial_1F_0\bigr).$$
--
--   These three operators are the entire vector-analytic vocabulary needed to state Maxwell's equations, Poynting's theorem and the Liénard–Wiechert field equations, and they are reusable in any other formalization of classical field theory.
--
--   **Formalization Note** Space is `EuclideanSpace ℝ (Fin 3)`, so the inner product and the norm come from Mathlib. Partial derivatives are taken with the Fréchet derivative along the standard basis vectors; at a point where the field fails to be differentiable the Fréchet derivative is the zero map by convention, and the divergence and curl there are $0$ rather than undefined.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section (the fields, the Poynting vector and the surface integral are all written in three-dimensional vector notation); J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, Chapter 6 and Appendix on vector formulas.

import Mathlib

namespace Larmor

/-- Three-dimensional Euclidean space, the arena for the electromagnetic fields. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `Vec`. -/
noncomputable def cross (u v : Vec) : Vec :=
  !₂[u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The derivative of the `i`-th component of a vector field `F` in the `j`-th
coordinate direction, at the point `x`. -/
noncomputable def partialDeriv (F : Vec → Vec) (j i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ F x (EuclideanSpace.single j 1) i

/-- The divergence of a vector field. -/
noncomputable def divg (F : Vec → Vec) (x : Vec) : ℝ := ∑ i, partialDeriv F i i x

/-- The curl of a vector field. -/
noncomputable def curl (F : Vec → Vec) (x : Vec) : Vec :=
  !₂[partialDeriv F 1 2 x - partialDeriv F 2 1 x,
     partialDeriv F 2 0 x - partialDeriv F 0 2 x,
     partialDeriv F 0 1 x - partialDeriv F 1 0 x]

end Larmor


