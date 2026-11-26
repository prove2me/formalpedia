-- Prove2me | Definitions.Def_Sendov_Common_Quadratic
-- name    : Sendov_Common_Quadratic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:54:00.829864+00:00
-- url     : https://prove2.me/theorems/58afbbde-c846-5398-a6d2-c1dfa8722b63
-- title:
--   Quadratic
-- statement:
--   Definitions and structural lemmas for Quadratic, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean

import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
namespace Sendov
noncomputable def QQ (c A t : ℝ) : ℝ := 1 - 2 * c * t + A * t ^ 2
variable {c A t : ℝ}
end Sendov


