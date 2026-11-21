-- Prove2me | Definitions.Def_cubic_surface_27_layer
-- name    : cubic_surface_27_layer
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T13:50:18.73943+00:00
-- url     : https://prove2.me/theorems/cdb247ef-af0d-42a9-81ca-563140700b56
-- title:
--   Cubic forms, smoothness, and lines over $\mathbb{C}$
-- statement:
--   This file fixes the concrete objects of the mission, over the complex numbers $\mathbb{C}$.
--
--   A **cubic form** is a homogeneous polynomial $F$ of degree $3$ in four variables, represented as an element of `MvPolynomial (Fin 4) ℂ`; the predicate `IsCubicForm F` asserts homogeneity of degree $3$. Its zero locus $V(F)\subset\mathbb{P}^3$ is the cubic surface.
--
--   The surface is **smooth** (`IsSmoothCubic F`) when the Jacobian criterion holds: for every nonzero vector $x\in\mathbb{C}^4$ with $F(x)=0$, at least one partial derivative $\partial F/\partial x_i$ is nonzero at $x$. Because $F$ is homogeneous, this condition is invariant under scaling $x$, so it is exactly smoothness of the projective surface $V(F)$.
--
--   A **line** on $V(F)$ is recorded as a $2$-dimensional linear subspace $W\subset\mathbb{C}^4$ on which $F$ vanishes identically; `linesOf F` is the set of all such subspaces. The projectivization of each such $W$ is a line contained in $V(F)$, and every line on $V(F)$ arises uniquely this way, so the cardinality of `linesOf F` is the number of lines on the surface.
--
--   **Formalization Note.** Homogeneity uses `MvPolynomial.IsHomogeneous`, partial derivatives use `MvPolynomial.pderiv`, and dimension uses `Module.finrank`. These definitions carry no axioms beyond the standard meanings; in particular they do not assume any count of lines.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora (author: Jack Huizenga, Penn State). Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, opening paragraph (definition of a cubic surface) and the Grassmannian section of Part II (a line as the projectivization of a 2-dimensional subspace of ℂ⁴).

import Mathlib

namespace CubicSurface27

/-- A cubic form in four variables over ℂ: a homogeneous polynomial of degree 3. -/
def IsCubicForm (F : MvPolynomial (Fin 4) ℂ) : Prop :=
  MvPolynomial.IsHomogeneous F 3

/-- Smoothness of the cubic surface V(F) ⊂ ℙ³, via the Jacobian criterion: at every nonzero
point of the affine cone over V(F), some partial derivative of F is nonzero. -/
def IsSmoothCubic (F : MvPolynomial (Fin 4) ℂ) : Prop :=
  ∀ x : Fin 4 → ℂ, x ≠ 0 → MvPolynomial.eval x F = 0 →
    ∃ i : Fin 4, MvPolynomial.eval x (MvPolynomial.pderiv i F) ≠ 0

/-- The lines on V(F): the 2-dimensional linear subspaces of ℂ⁴ on which F vanishes
identically. Their projectivizations are exactly the lines contained in the surface. -/
noncomputable def linesOf (F : MvPolynomial (Fin 4) ℂ) : Set (Submodule ℂ (Fin 4 → ℂ)) :=
  {W | Module.finrank ℂ W = 2 ∧ ∀ x ∈ W, MvPolynomial.eval x F = 0}

end CubicSurface27


