-- Prove2me | Definitions.Def_LocalPush_SDD
-- name    : LocalPush_SDD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:03:37.781981+00:00
-- url     : https://prove2.me/theorems/a5d56a8f-7697-490b-bda0-ad64ddb8bc34
-- title:
--   Symmetric diagonally dominant matrices and the energy norm $\|x\|_S=\sqrt{x^\top Sx}$
-- statement:
--   A real square matrix $M$ is symmetric diagonally dominant (SDD) if it is symmetric and each diagonal entry is at least the sum of the absolute values of the other entries in its row:
--   $$M_{ii}\ \ge\ \sum_{j\neq i}|M_{ij}|\qquad\text{for every } i.$$
--   For a symmetric positive definite matrix $M$ and a vector $x$, the energy norm is $\|x\|_M:=\sqrt{x^\top Mx}$.
--
--   These notions state the guarantee (6) of the SDD solver used by the algorithm.
--
--   **Formalization Note** The energy norm is applied only to positive definite matrices, where $x^\top Mx\ge 0$.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §4, "SDD solver", p.15 (PDF p.15)

import Mathlib

open Finset Matrix

namespace LocalPush

/-!
# Symmetric diagonally dominant matrices and the energy norm

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §4, "SDD solver", p.15 (PDF p.15).

"We call a square matrix symmetric diagonally dominant (SDD) if it is symmetric and each of its diagonal entries
is at least the sum of the absolute values of the other entries in the same row. […] For a vector x and a
symmetric positive definite matrix S, define the energy norm as ‖x‖_S := √(xᵀSx) = ‖S^{1/2}x‖₂."

**Formalization Note.**
* Matrices are real and indexed by any finite type with decidable equality.
* `enorm M x := √(xᵀMx)` is used only for positive definite `M`, where `xᵀMx ≥ 0`; `Real.sqrt` would return `0`
  on a negative argument, which never occurs there.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `M` is symmetric diagonally dominant: symmetric, and `∑_{j ≠ i} |M i j| ≤ M i i` for every row `i`. -/
def IsSDD (M : Matrix ι ι ℝ) : Prop :=
  M.IsSymm ∧ ∀ i, ∑ j ∈ univ.erase i, |M i j| ≤ M i i

/-- The energy norm `‖x‖_M := √(xᵀMx)`. -/
noncomputable def enorm (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ (M *ᵥ x))

end LocalPush


