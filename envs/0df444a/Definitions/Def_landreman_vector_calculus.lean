-- Prove2me | Definitions.Def_landreman_vector_calculus
-- name    : landreman_vector_calculus
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T18:41:33.818281+00:00
-- url     : https://prove2.me/theorems/dd0de590-9a6d-4526-9723-833d352f2e96
-- title:
--   Gradient, divergence, curl and tension on $\mathbb R^3$
-- statement:
--   This file fixes the vector-calculus vocabulary used throughout the mission.
--
--   Cartesian three-space is modelled as the space of coordinate functions on three indices, written $\mathbb R^3$ below, with coordinates $x_0, x_1, x_2$ (the $x$, $y$, $z$ of the source paper). For a scalar field $f:\mathbb R^3\to\mathbb R$ the partial derivative $\partial_i f$ is the Fréchet derivative of $f$ evaluated on the $i$-th standard basis vector, and the gradient is $\nabla f=(\partial_0 f,\partial_1 f,\partial_2 f)$.
--
--   For a vector field $V:\mathbb R^3\to\mathbb R^3$ with components $V_0,V_1,V_2$ the file defines
--
--   $$\nabla\cdot V=\sum_{i} \partial_i V_i,\qquad
--   \nabla\times V=\big(\partial_1 V_2-\partial_2 V_1,\ \partial_2 V_0-\partial_0 V_2,\ \partial_0 V_1-\partial_1 V_0\big),$$
--
--   the cross product $u\times w$ with its usual components, the squared Euclidean length $|u|^2=\sum_i u_i^2$, the directional derivative $V\cdot\nabla f=\sum_j V_j\,\partial_j f$, and the tension field $\big((V\cdot\nabla)V\big)_i=V\cdot\nabla V_i$.
--
--   These are the operators in which the MHD equilibrium equations $(\nabla\times B)\times B=\nabla p$ and $\nabla\cdot B=0$ are written. They are stated for arbitrary fields, so they are reusable for any development of vector calculus on $\mathbb R^3$ that does not need differential forms.
--
--   **Formalization Note.** Every derivative is taken in the sense of the Fréchet derivative, which returns a junk value when the function is not differentiable at the point; statements using these operators therefore always carry a hypothesis placing the point in the open domain where the fields are smooth. Squared length is defined by the explicit sum rather than by a norm, so no inner-product structure is imposed on the coordinate space.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (1.1) (operators used to state the equilibrium equations)

import Mathlib

namespace Landreman3DEquilibria

/-- Cartesian three-space, coordinates indexed by `Fin 3` (`0 = x`, `1 = y`, `2 = z`). -/
abbrev LVec : Type := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field. -/
noncomputable def partialD (f : LVec → ℝ) (i : Fin 3) (x : LVec) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The gradient `∇ f` of a scalar field. -/
noncomputable def grad (f : LVec → ℝ) (x : LVec) : LVec := fun i => partialD f i x

/-- The divergence `∇ · V` of a vector field. -/
noncomputable def divg (V : LVec → LVec) (x : LVec) : ℝ :=
  ∑ i : Fin 3, partialD (fun y => V y i) i x

/-- The curl `∇ × V` of a vector field. -/
noncomputable def curl (V : LVec → LVec) (x : LVec) : LVec :=
  ![partialD (fun y => V y 2) 1 x - partialD (fun y => V y 1) 2 x,
    partialD (fun y => V y 0) 2 x - partialD (fun y => V y 2) 0 x,
    partialD (fun y => V y 1) 0 x - partialD (fun y => V y 0) 1 x]

/-- The cross product `u × w` in Cartesian three-space. -/
def cross3 (u w : LVec) : LVec :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

/-- The squared Euclidean length `|u|²`. -/
def normSq (u : LVec) : ℝ := ∑ i : Fin 3, u i ^ 2

/-- The directional derivative `V · ∇ f` of a scalar field along a vector field. -/
noncomputable def advect (V : LVec → LVec) (f : LVec → ℝ) (x : LVec) : ℝ :=
  ∑ j : Fin 3, V x j * partialD f j x

/-- The tension term `(V · ∇) V` of a vector field. -/
noncomputable def tension (V : LVec → LVec) (x : LVec) : LVec :=
  fun i => advect V (fun y => V y i) x

end Landreman3DEquilibria


