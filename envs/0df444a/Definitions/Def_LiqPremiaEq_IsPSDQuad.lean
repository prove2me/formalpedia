-- Prove2me | Definitions.Def_LiqPremiaEq_IsPSDQuad
-- name    : LiqPremiaEq_IsPSDQuad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:59.910057+00:00
-- url     : https://prove2.me/theorems/503e8a14-edf6-424a-9d9d-3518a3c8860b
-- title:
--   Positive (semi)definite matrices without symmetry: $b^\top Ab\ge 0$ (resp. $>0$)
-- statement:
--   A square real matrix $A$ is **positive semidefinite** if
--
--   $$b^\top A b\ge 0\qquad\text{for all vectors } b,$$
--
--   and **positive definite** if $b^\top Ab>0$ for every $b\neq 0$. No symmetry of $A$ is required: as the paper stresses (footnotes 10 and 19), the risk-aversion matrix $\Gamma$ and the Riccati solution $F$ are not symmetric, and a non-symmetric positive definite matrix need not have real eigenvalues.
--
--   These are the notions in Lemmas 7.1, 7.4, 7.5, 7.6, Corollary 7.7 and Lemma 4.4.
--
--   **Formalization Note** `IsPSDQuad` and `IsPDQuad` are deliberately not Mathlib's `Matrix.PosSemidef`/`Matrix.PosDef`, which require the matrix to be Hermitian.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, footnote 10, p.8; footnote 19 and Lemma 7.1, p.14

import Mathlib

open Matrix

namespace LiqPremiaEq

/-- A square real matrix `A` is **positive semidefinite** in the quadratic-form sense:
`bᵀ A b ≥ 0` for every vector `b`. No symmetry is required.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, footnote 10 (p.8) and footnote 19 (p.14):
"In much of the literature, positive definite matrices are additionally required to be
symmetric. This does not generally hold for F, however".

**Formalization Note** This is deliberately not Mathlib's `Matrix.PosSemidef`, which also
requires `IsHermitian`; the risk-aversion matrix `Γ` and the Riccati solution `F` of the paper
are not symmetric. -/
def IsPSDQuad {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ b : ι → ℝ, 0 ≤ b ⬝ᵥ (A *ᵥ b)

/-- A square real matrix `A` is **positive definite** in the quadratic-form sense:
`bᵀ A b > 0` for every nonzero vector `b`. No symmetry is required.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, footnote 19, p.14, and Lemma 7.1, p.14 ("it remains to
show that b⊤Γb > 0 for all b ∈ ℝᴹ∖{0}").

**Formalization Note** Not Mathlib's `Matrix.PosDef` (which requires `IsHermitian`). -/
def IsPDQuad {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ b : ι → ℝ, b ≠ 0 → 0 < b ⬝ᵥ (A *ᵥ b)

end LiqPremiaEq


