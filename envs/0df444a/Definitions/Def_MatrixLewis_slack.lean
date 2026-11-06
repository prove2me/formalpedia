-- Prove2me | Definitions.Def_MatrixLewis_slack
-- name    : MatrixLewis_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:30.524204+00:00
-- url     : https://prove2.me/theorems/079c8a01-fdb7-4bfc-b48c-5c85664764a3
-- title:
--   Slack $S_x=\sum_i x_iA_i-C$ and domain $\mathcal D=\{x:S_x\succ0\}$
-- statement:
--   Given $A_1,\dots,A_m,C\in\mathbb S^n$, the **slack** of $x\in\mathbb R^m$ is
--   $$
--   S_x:=\mathcal A x-C=\sum_{i=1}^m x_iA_i-C ,
--   $$
--   and the **domain** is the set of strictly feasible points of the semidefinite program,
--   $$
--   \mathcal D:=\{x\in\mathbb R^m : S_x\succ 0\}.
--   $$
--
--   **Formalization Note** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`; $S\succ0$ is `Matrix.PosDef`, which includes symmetry (automatic for symmetric data).
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15

import Mathlib

namespace MatrixLewis

/-- The slack `S_x := 𝒜x − C = ∑ᵢ xᵢAᵢ − C` of the semidefinite program (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1,
p.15). Points are `x ∈ ℝᵐ`, encoded as `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def slack {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, x i • A i - C

/-- The domain `𝒟 := {x ∈ ℝᵐ : S_x ≻ 0}` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15): the strictly feasible
points. `Matrix.PosDef` includes symmetry, which holds automatically for symmetric data. -/
def dom {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | (slack A C x).PosDef}

end MatrixLewis


