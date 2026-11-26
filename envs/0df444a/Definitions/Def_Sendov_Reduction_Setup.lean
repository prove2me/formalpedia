-- Prove2me | Definitions.Def_Sendov_Reduction_Setup
-- name    : Sendov_Reduction_Setup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:42:00.101501+00:00
-- url     : https://prove2.me/theorems/f44739db-b416-4a4c-a5a2-e5f4fc1e2154
-- title:
--   Setup
-- statement:
--   Definitions and structural lemmas for Setup, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean

import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
namespace Sendov
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2
variable {n : ℕ} {a x t α : ℝ}
end Sendov


