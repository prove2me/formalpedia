-- Prove2me | Definitions.Def_GevreyGibbsSep_iterPartial
-- name    : GevreyGibbsSep_iterPartial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:59.437207+00:00
-- url     : https://prove2.me/theorems/35c44243-18cf-4bfd-86bc-2d6c997d4de9
-- title:
--   Iterated partial derivatives $\partial_{i_1}\cdots\partial_{i_j}f$
-- statement:
--   For a list of coordinates $(i_1,\dots,i_j)$ and a function $f:\mathbb R^d\to\mathbb R$, this is the iterated partial derivative
--   $$\partial_{i_1}\partial_{i_2}\cdots\partial_{i_j}f,$$
--   with the empty list giving $f$ itself. These are the entries of the derivative tensors $\nabla^{\otimes j}f$ of Definition B.2, and the building block of the multi-index derivatives $\partial^a$.
--
--   **Formalization Note** Each step is the Fréchet derivative in the direction $e_i$. Where a function is not differentiable, Mathlib's derivative is $0$; every statement applies it to smooth functions or at interior points of a set where the function is smooth.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section II, p.5; Definition B.2, p.34

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Iterated coordinate partial derivatives: `iterPartial [i₁, …, iⱼ] f = ∂_{i₁} ⋯ ∂_{iⱼ} f`
(arXiv:2608.24527 (sha256 d4fd40eb…), p.5: `∂^a = ∏_j (∂/∂x_j)^{a_j}`; Definition B.2, p.34:
the entries of `∇^{⊗j}`).

**Formalization Note** Each step is the Fréchet derivative in the direction `e_i`; for a function
that is not differentiable at a point, Mathlib's `fderiv` returns `0` there. Every statement
applies it to smooth functions, or at interior points of a set where the function is smooth. -/
noncomputable def iterPartial {d : ℕ} :
    List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], f => f
  | i :: l, f => fun x => fderiv ℝ (iterPartial l f) x (Pi.single i 1)

end GevreyGibbsSep


