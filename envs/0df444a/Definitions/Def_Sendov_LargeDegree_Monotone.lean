-- Prove2me | Definitions.Def_Sendov_LargeDegree_Monotone
-- name    : Sendov_LargeDegree_Monotone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:02:20.238499+00:00
-- url     : https://prove2.me/theorems/bd444116-d45e-4a6c-8d2e-dd4ffeba9ff0
-- title:
--   Monotone
-- statement:
--   Definitions and structural lemmas for Monotone, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean

import Definitions.Def_Sendov_LargeDegree_Tail
set_option autoImplicit false
namespace Sendov
variable {n : ℕ} {α : ℝ}
noncomputable def T1 (n : ℕ) (α : ℝ) : ℝ :=
  24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
    ((3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4))
noncomputable def T2 (n : ℕ) (α : ℝ) : ℝ :=
  A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (16 * (3 + α)) * Real.sqrt (α / (3 + α)) ^ (n - 4)
noncomputable def Ut (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / 200 + 1 / (400 * (3 + α)) + 101 / 100 * T1 101 α
    + (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48
end Sendov


