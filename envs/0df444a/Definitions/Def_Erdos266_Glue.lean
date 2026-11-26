-- Prove2me | Definitions.Def_Erdos266_Glue
-- name    : Erdos266_Glue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:30:58.87784+00:00
-- url     : https://prove2.me/theorems/4a9e4716-a1d3-5f08-a8b6-56be73a6618e
-- title:
--   Glue
-- statement:
--   Definitions and structural lemmas for Glue, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Glue.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
def RationalShifts (a : ℕ → ℕ) : Prop :=
  ∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
    ∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q
end Erdos266


