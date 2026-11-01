-- Prove2me | Definitions.Def_ParetoIneff_IsWellBehaved
-- name    : ParetoIneff_IsWellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:11.547994+00:00
-- url     : https://prove2.me/theorems/8c38e223-5d1b-4f57-801a-f1d43a86a9f8
-- title:
--   Well-behaved task
-- statement:
--   A task with component $\mathcal A_j$ is **well-behaved** if, for all true canonical cost vectors, $\mathcal A_j$ allocates the task to the fast machine on all equilibria.
--
--   This is the dichotomy behind Theorem 6: tasks that are not well-behaved force a large Price of Anarchy, and well-behaved tasks force a large Price of Stability.
--
--   **Formalization Note** The notion is relative to the fixed dummy list.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 5, p.13

import Mathlib
import Definitions.Def_ParetoIneff_SingleTaskMech_IsEq
import Definitions.Def_ParetoIneff_IsCanonical

open NNReal

namespace ParetoIneff

/-- A task with component `A` is **well-behaved**, Definition 5, arXiv:1809.03454v7, p.13: for all
true canonical cost vectors `v` (with dummy list `d`), `A` allocates the task to the fast machine on
all equilibria. -/
def IsWellBehaved {n : ℕ} (α : ℝ) (d : Fin (n - 2) → ℝ≥0) (A : SingleTaskMech n) : Prop :=
  ∀ (v : Fin n → ℝ≥0) (fast slow : Fin n), IsCanonical α d v fast slow →
    ∀ s : Fin n → ℝ≥0, A.IsEq v s → A.alloc s = fast

end ParetoIneff


