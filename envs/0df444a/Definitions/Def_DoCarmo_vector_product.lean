-- Prove2me | Definitions.Def_DoCarmo_vector_product
-- name    : DoCarmo_vector_product
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T00:12:42.89056+00:00
-- url     : https://prove2.me/theorems/418b1d3e-35b3-49bc-8100-9231e798ef6b
-- title:
--   Vector product in $\mathbb{R}^3$ and rigid motions
-- statement:
--   Two basic notions of Euclidean $3$-space used throughout do Carmo's Chapter 1.
--
--   The **vector product** of $u, v \in \mathbb{R}^3$ is
--
--   $$ u \wedge v = (u_1v_2 - u_2v_1,\ u_2v_0 - u_0v_2,\ u_0v_1 - u_1v_0), $$
--
--   the unique vector orthogonal to $u$ and $v$ whose length is the area of the parallelogram they span and for which $\{u, v, u \wedge v\}$ is positively oriented (do Carmo §1-4).
--
--   A **rigid motion** of $\mathbb{R}^3$ is the composition of an orthogonal linear map $\rho$ with $\det \rho > 0$ and a translation by a vector $c$, that is, $M(p) = \rho(p) + c$ (do Carmo §1-5, Exercise 6). The determinant condition is included because rigid motions are expected to preserve orientation.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-4 (pp. 12-15), and Section 1-5, Exercise 6 (p. 23)

import Mathlib

namespace DoCarmoDG

/-- The vector product (cross product) `u ∧ v` of two vectors of `ℝ³`,
do Carmo, *Differential Geometry of Curves and Surfaces*, §1-4, Eq. (1). -/
noncomputable def cross (u v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- A rigid motion of `ℝ³`: an orthogonal linear map with positive determinant, followed by a
translation, do Carmo §1-5, Exercise 6. -/
def IsRigidMotion (M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ (rho : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 3)),
    0 < LinearMap.det (rho.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
      ∧ ∀ x, M x = rho x + c

end DoCarmoDG


