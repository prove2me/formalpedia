-- Prove2me | Definitions.Def_L0BnB_Relax_rss
-- name    : L0BnB_Relax_rss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:34.608987+00:00
-- url     : https://prove2.me/theorems/de14c2e6-4ca8-41a4-8cb9-13881ea6aaed
-- title:
--   Least-squares loss $\frac12\|y-X\beta\|_2^2$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ be a data matrix and $y\in\mathbb R^n$ a response vector. For coefficients $\beta\in\mathbb R^p$ the **least-squares loss** is
--
--   $$\frac12\|y-X\beta\|_2^2=\frac12\sum_{j=1}^n\bigl(y_j-(X\beta)_j\bigr)^2 .$$
--
--   It is the data-fitting term shared by problem (1), the Big-M formulation (2), the perspective formulation (3) and the reduced objectives $G$ and $H$.
--
--   **Formalization Note** The squared Euclidean norm is written out as a sum of squares, because Lean's default norm on $\mathbb R^n$ (functions `Fin n → ℝ`) is the sup norm. The index sets are `Fin n`, `Fin p` (0-based).
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, problem (1), p. 2; notation, p. 4

import Mathlib

namespace L0BnB.Relax

/-- **Least-squares loss `½‖y − Xβ‖²₂`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, problem (1), p. 2 (the term `(1/2)‖y − Xβ‖²₂`); notation p. 4: "We let
`‖·‖q` denote the standard ℓq norm with q ∈ {0, 1, 2, ∞}."

`rss X y β = ½ ∑_j (y_j − (Xβ)_j)²` for a data matrix `X ∈ ℝ^{n×p}`, a response `y ∈ ℝⁿ` and
coefficients `β ∈ ℝᵖ`; `X.mulVec β` is the matrix–vector product `Xβ`.

**Formalization Note.** The squared Euclidean norm is written out as a sum of squares
(paper.md Reading 5): Lean's norm on `Fin n → ℝ` is the sup norm, so `‖y - X.mulVec β‖ ^ 2` would
be a different loss. The index sets `[n]`, `[p]` (1-based in the paper) are `Fin n`, `Fin p`
(0-based); no statement depends on the base. -/
noncomputable def rss {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / 2) * ∑ j, (y j - (X.mulVec β) j) ^ 2

end L0BnB.Relax


