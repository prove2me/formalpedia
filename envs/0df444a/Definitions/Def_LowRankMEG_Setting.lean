-- Prove2me | Definitions.Def_LowRankMEG_Setting
-- name    : LowRankMEG_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:45.309583+00:00
-- url     : https://prove2.me/theorems/1d50aa42-18fa-4aa1-9a92-bb2e742abe5e
-- title:
--   The standing assumptions on $f$ and $\nabla f$
-- statement:
--   Problem (1) minimizes a function $f:\mathbb R^{n\times n}\to\mathbb R$ over $\mathcal S_n$. Throughout the paper:
--
--   1. $f$ is convex on $\mathbb R^{n\times n}$;
--   2. the gradient of $f$ is symmetric on symmetric matrices, $\nabla f(X)\in\mathbb S^n$ for all $X\in\mathbb S^n$;
--   3. $f$ is $\beta$-smooth over $\mathcal S_n$ in the sense
--   $$
--   \|\nabla f(X)-\nabla f(Y)\|_2\le\beta\|X-Y\|_*\qquad\text{for all }X,Y\in\mathcal S_n,
--   $$
--   where $\|\cdot\|_2$ is the spectral norm and $\|\cdot\|_*$ the nuclear norm.
--
--   These assumptions are stated once, on the first page, and bind every result that involves $f$.
--
--   **Formalization Note** `grad` is the map $X\mapsto\nabla f(X)$. It is tied to $f$ by Fréchet differentiability at each symmetric $X$ with derivative $H\mapsto\operatorname{Tr}(\nabla f(X)H)$. The Frobenius norm only serves to state differentiability; all norms on $\mathbb R^{n\times n}$ give the same derivative.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, §1, p.1

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
open scoped Matrix.Norms.Frobenius

namespace LowRankMEG

/-- **The standing assumptions on the objective of Problem (1).**
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, §1, p.1: `f : ℝ^{n×n} → ℝ` is convex, its gradient is a symmetric matrix on `𝕊ⁿ`, and
`‖∇f(X) − ∇f(Y)‖₂ ≤ β‖X − Y‖_*` for all `X, Y ∈ 𝒮_n`.

**Formalization Note.** `grad` is the map `X ↦ ∇f(X)`. The clause `hasGrad` ties it to `f`: at each
symmetric `X`, `f` is Fréchet differentiable as a function on `ℝ^{n×n}` with derivative
`H ↦ Tr(∇f(X) H)`, the paper's `⟨∇f(X), H⟩`. The Frobenius norm only serves to state `HasFDerivAt`; all
norms on `ℝ^{n×n}` give the same derivative. `‖·‖₂` is `WainwrightHDS.NucNorm.opNorm2`, the spectral norm,
and `‖·‖_*` is `WainwrightHDS.NucNorm.nucNorm`, the sum of the singular values. The values of `grad` off
`𝕊ⁿ` are unconstrained and no statement uses them. -/
structure Setting {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) (β : ℝ) : Prop where
  /-- `f` is convex on `ℝ^{n×n}`. -/
  convex : ConvexOn ℝ Set.univ f
  /-- `grad X` is the gradient of `f` at every symmetric `X`. -/
  hasGrad : ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsSymm →
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ, HasFDerivAt f L X ∧ ∀ H, L H = (grad X * H).trace
  /-- `∇f(X) ∈ 𝕊ⁿ` for all `X ∈ 𝕊ⁿ`. -/
  symm : ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsSymm → (grad X).IsSymm
  /-- `‖∇f(X) − ∇f(Y)‖₂ ≤ β‖X − Y‖_*` on the spectrahedron. -/
  smooth : ∀ X ∈ PSDPolyApprox.densityMatrices n, ∀ Y ∈ PSDPolyApprox.densityMatrices n,
    WainwrightHDS.NucNorm.opNorm2 (grad X - grad Y) ≤ β * WainwrightHDS.NucNorm.nucNorm (X - Y)

end LowRankMEG


