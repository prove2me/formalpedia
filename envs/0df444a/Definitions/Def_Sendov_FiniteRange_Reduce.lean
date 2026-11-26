-- Prove2me | Definitions.Def_Sendov_FiniteRange_Reduce
-- name    : Sendov_FiniteRange_Reduce
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:56:01.758487+00:00
-- url     : https://prove2.me/theorems/1c11524d-1a46-52b7-8fd6-95ec61694ab3
-- title:
--   Reduce
-- statement:
--   Definitions and structural lemmas for Reduce, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
set_option autoImplicit false
namespace Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
end Sendov


