-- Prove2me | Definitions.Def_ConstrSOSP_Poly
-- name    : ConstrSOSP_Poly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:22.177107+00:00
-- url     : https://prove2.me/theorems/d15bfd82-2ca8-4d54-8117-f72389082791
-- title:
--   Polytope $\mathcal X=\{x:Ax\le b\}$
-- statement:
--   For $A\in\mathbb R^{m\times d}$ with rows $A_j$ and $b\in\mathbb R^m$, the feasible set of problem (3) is
--   $$
--   \mathcal X=\{x\in\mathbb R^d:\ A_jx\le b_j\ \text{for all } j\}.
--   $$
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.2, (3), p.18

import Mathlib

namespace ConstrSOSP

/-- **The polytope `X = {x ∈ ℝᵈ : Ax ≤ b}`** of problem (3) (arXiv:2604.02285, 2 Nov 2026, §4.2,
p.18: "min_x f(x), x ∈ X := {x ∈ ℝ^d : Ax ≤ b}", with `A ∈ ℝ^{m×d}`, `b ∈ ℝᵐ`).

`A j` is the `j`-th row of `A`; `x ∈ Poly A b` iff `A j ⬝ x ≤ b j` for every row `j`. -/
def Poly {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ j, A j ⬝ᵥ x ≤ b j}

end ConstrSOSP


