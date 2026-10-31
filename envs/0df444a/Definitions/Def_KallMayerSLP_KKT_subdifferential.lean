-- Prove2me | Definitions.Def_KallMayerSLP_KKT_subdifferential
-- name    : KallMayerSLP_KKT_subdifferential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:45.4007+00:00
-- url     : https://prove2.me/theorems/96f150f7-30dc-4a96-b74a-358df9110344
-- title:
--   Subdifferential $\partial\varphi(x)$ (Definition 3.2)
-- statement:
--   A vector $g\in\mathbb R^n$ is a **subgradient** of a function $\varphi:\mathbb R^n\to\mathbb R$ at $x$ if
--   $$
--   g^{\mathsf T}(z-x)\le\varphi(z)-\varphi(x)\qquad\forall z\in\mathbb R^n .
--   $$
--   The set of all subgradients of $\varphi$ at $x$ is the **subdifferential** $\partial\varphi(x)$.
--
--   Proposition 3.2 describes this set for convex $\varphi$.
--
--   **Formalization Note** The book defines subgradients for convex $\varphi$; the Lean set is defined for every $\varphi$, and every theorem about it assumes convexity.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, Definition 3.2, p.61 (PDF 72)

import Mathlib

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **Subgradients and the subdifferential `∂φ(x)` (Definition 3.2).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, Definition 3.2, p.61
(PDF 72): "A vector `g ∈ ℝⁿ` is a subgradient of a convex function `φ` at a point `x`, if
`gᵀ(z − x) ≤ φ(z) − φ(x) ∀z`. The set of all subgradients of `φ` at `x` is the subdifferential of
`φ` at `x`, denoted by `∂φ(x)`."

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` and `gᵀ(z − x)` is `⟪g, z - x⟫`. The
set is defined for every `φ : ℝⁿ → ℝ`; the book only uses it for convex `φ`, and every theorem
about it assumes convexity. -/
def subdifferential {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {g | ∀ z, ⟪g, z - x⟫ ≤ φ z - φ x}

end KallMayerSLP.KKT


