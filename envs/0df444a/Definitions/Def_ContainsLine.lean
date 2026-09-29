-- Prove2me | Definitions.Def_ContainsLine
-- name    : ContainsLine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:38.485727+00:00
-- url     : https://prove2.me/theorems/b3c11713-4936-4007-af9f-83fba76ec216
-- title:
--   Polyhedron containing a line
-- statement:
--   **(Definition 2.12)** A polyhedron $P \subset \mathbb{R}^n$ *contains a line* if there exists a vector $x \in P$ and a nonzero vector $d \in \mathbb{R}^n$ such that
--
--   $$x + \lambda d \in P$$
--
--   for all scalars $\lambda$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 2.12, p. 63

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
Polyhedra containing a line.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 2.12 (p. 63)**: "A polyhedron
`P ⊆ ℝⁿ` *contains a line* if there exists a vector `x ∈ P` and a nonzero
vector `d ∈ ℝⁿ` such that `x + λd ∈ P` for all scalars `λ`."
-/

namespace LinearOptimization

/-- **B&T Definition 2.12 (p. 63).** `S` contains a line: some `x ∈ S` and
nonzero direction `d` with `x + λ•d ∈ S` for every scalar `λ`. -/
def ContainsLine {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ x ∈ S, ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ lam : ℝ, x + lam • d ∈ S

end LinearOptimization


