-- Prove2me | Definitions.Def_DoCarmo_local_theory_curves
-- name    : DoCarmo_local_theory_curves
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T00:15:44.495295+00:00
-- url     : https://prove2.me/theorems/b5723c9b-9204-46b6-96ea-247a6db96688
-- title:
--   Arc length, curvature, Frenet trihedron and torsion of a space curve
-- statement:
--   The vocabulary of do Carmo §1-5, the local theory of curves parametrized by arc length.
--
--   A curve $\alpha : I \to \mathbb{R}^3$ is **parametrized by arc length** when it is smooth on $I$ and $|\alpha'(s)| = 1$ for all $s \in I$. Its **unit tangent** is $t(s) = \alpha'(s)$ and its **curvature** is $k(s) = |\alpha''(s)|$.
--
--   At points where $k(s) \neq 0$ the **normal vector** $n(s)$ is the unit vector with $\alpha''(s) = k(s)\,n(s)$, and the **binormal** is $b(s) = t(s) \wedge n(s)$. Since $b$ is a unit vector and $b' = t \wedge n'$ is orthogonal to $t$, the derivative $b'(s)$ is a multiple of $n(s)$, and the **torsion** $\tau(s)$ is defined by $b'(s) = \tau(s)\,n(s)$; equivalently, and as formalized here, $\tau(s) = \langle b'(s), n(s)\rangle$.
--
--   This is do Carmo's sign convention for the torsion; many other authors write $-\tau$ for the same quantity.
--
--   The formalization uses total functions $\mathbb{R} \to \mathbb{R}^3$ that are required to be smooth and unit-speed only on $I$. All theorems in this mission take $I$ to be an **open** interval $(a,b)$, so that the ordinary derivative agrees with the derivative along $I$ at every point of $I$. Where $k(s) = 0$ the normal, binormal and torsion take junk values, so every statement mentioning them assumes $k \neq 0$ explicitly.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_vector_product

namespace DoCarmoDG

/-- A curve `α : I → ℝ³` parametrized by arc length: `α` is smooth on `I` and its velocity
has unit length at every point of `I`.  do Carmo, §1-3 and §1-5.
All statements below use an **open** interval `I`, so that `deriv` is the honest derivative
at every point of `I`. -/
def IsArcLengthCurve (I : Set ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) α I ∧ ∀ s ∈ I, ‖deriv α s‖ = 1

/-- The unit tangent vector `t(s) = α'(s)` of a curve parametrized by arc length, do Carmo §1-5. -/
noncomputable def tangent (α : ℝ → EuclideanSpace ℝ (Fin 3)) : ℝ → EuclideanSpace ℝ (Fin 3) :=
  deriv α

/-- The curvature `k(s) = |α''(s)|` of a curve parametrized by arc length, do Carmo §1-5. -/
noncomputable def curvature (α : ℝ → EuclideanSpace ℝ (Fin 3)) (s : ℝ) : ℝ :=
  ‖deriv (deriv α) s‖

/-- The normal vector `n(s)`, the unit vector in the direction of `α''(s)`, defined by
`α''(s) = k(s) n(s)` at points where `k(s) ≠ 0`, do Carmo §1-5. -/
noncomputable def normal (α : ℝ → EuclideanSpace ℝ (Fin 3)) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (curvature α s)⁻¹ • deriv (deriv α) s

/-- The binormal vector `b(s) = t(s) ∧ n(s)`, do Carmo §1-5. -/
noncomputable def binormal (α : ℝ → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  cross (tangent α s) (normal α s)

/-- The torsion `τ(s)`, defined by `b'(s) = τ(s) n(s)`, do Carmo §1-5.
(do Carmo's sign convention: many authors write `-τ` for this quantity.) -/
noncomputable def torsion (α : ℝ → EuclideanSpace ℝ (Fin 3)) (s : ℝ) : ℝ :=
  inner ℝ (deriv (binormal α) s) (normal α s)

end DoCarmoDG


