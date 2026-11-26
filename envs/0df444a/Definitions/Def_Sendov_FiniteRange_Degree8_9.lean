-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree8_9
-- name    : Sendov_FiniteRange_Degree8_9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:04:20.421199+00:00
-- url     : https://prove2.me/theorems/95574c28-9888-5d43-a64d-d29c19861291
-- title:
--   Degree8 9
-- statement:
--   Definitions and structural lemmas for Degree8 9, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B8_9
def Lc : ℤ := 840
def betac : ℤ := 63228481
def tauc : ℤ := 304104393583393026770083796931785379693060776623910754345993
def Nmomc : List ℤ :=
  [5292, 15960, 40620, 3056, 80]
end B8_9
end Sendov


