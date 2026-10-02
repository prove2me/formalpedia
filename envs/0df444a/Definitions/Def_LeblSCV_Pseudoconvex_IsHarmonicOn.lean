-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsHarmonicOn
-- name    : LeblSCV_Pseudoconvex_IsHarmonicOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:38:29.882457+00:00
-- url     : https://prove2.me/theorems/f46a42f8-3d0b-4c21-9348-c5dae219e532
-- title:
--   Definition 2.4.1 — harmonic function (on an open subset of ℂ)
-- statement:
--   Let $U \subset \mathbb{C} \cong \mathbb{R}^2$ be open. A $C^2$-smooth function $f : U \to \mathbb{R}$ is **harmonic** if its Laplacian vanishes on $U$:
--   $$\nabla^2 f = \frac{\partial^2 f}{\partial x^2} + \frac{\partial^2 f}{\partial y^2} = 0 \quad \text{on } U.$$
--
--   Harmonic functions are the comparison functions in the definition of subharmonic functions.
--
--   **Formalization Note.** Only the case $\mathbb{R}^2 = \mathbb{C}$ of the book's definition (stated for open $U \subset \mathbb{R}^n$) is formalized; it is the only case the chapter uses. $\nabla^2$ is Mathlib's Laplacian on the real inner product space $\mathbb{C}$. $f$ is a function on all of $\mathbb{C}$ whose values off $U$ play no role.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 78, Definition 2.4.1

import Mathlib

open InnerProductSpace Laplacian

namespace LeblSCV.Pseudoconvex

/-- Definition 2.4.1, first part (Lebl, p. 78), for open `U ⊂ ℂ ≅ ℝ²`: a `C²`-smooth
`f : U → ℝ` is *harmonic* if its Laplacian `∇²f = ∂²f/∂x² + ∂²f/∂y²` vanishes on `U`.
`Δ` is Mathlib's Laplacian on the real inner product space `ℂ`; values of `f` off `U` are
irrelevant. -/
def IsHarmonicOn (f : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ContDiffOn ℝ 2 f U ∧ ∀ z ∈ U, Δ f z = 0

end LeblSCV.Pseudoconvex


