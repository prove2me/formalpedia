-- Prove2me | Definitions.Def_Sendov_Defs
-- name    : Sendov_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:52:49.765889+00:00
-- url     : https://prove2.me/theorems/62068306-b8ec-40b1-b407-448ed86df3cf
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Defs.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
namespace Sendov
noncomputable def M (n : ℕ) : ℝ := (n : ℝ) - 1
noncomputable def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / M n
noncomputable def c (n : ℕ) (α : ℝ) : ℝ := 1 - α / M n - α / (2 * (3 + α))
noncomputable def Q (n : ℕ) (α : ℝ) (t : ℝ) : ℝ := 1 - 2 * c n α * t + A n α * t ^ 2
noncomputable def R (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
    A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) *
      ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)
end Sendov


