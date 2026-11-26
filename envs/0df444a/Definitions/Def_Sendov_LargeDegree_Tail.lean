-- Prove2me | Definitions.Def_Sendov_LargeDegree_Tail
-- name    : Sendov_LargeDegree_Tail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:01:38.448279+00:00
-- url     : https://prove2.me/theorems/59786891-33b7-46a5-9561-a76e9ff79f3a
-- title:
--   Tail
-- statement:
--   Definitions and structural lemmas for Tail, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean

import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
namespace Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}
noncomputable def U (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
    + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      * (6 / (c n α ^ 4 *
            ((((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
              * (((n : ℝ) - 4) / 2 + 4)))
        + (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) / 4)
end Sendov


