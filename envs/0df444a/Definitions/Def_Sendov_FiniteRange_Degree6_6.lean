-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree6_6
-- name    : Sendov_FiniteRange_Degree6_6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:03:48.227342+00:00
-- url     : https://prove2.me/theorems/05efa708-e843-4671-b7b8-9288dab547ab
-- title:
--   Degree6 6
-- statement:
--   Definitions and structural lemmas for Degree6 6, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B6_6
def Lc : ℤ := 60
def betac : ℤ := 17041
def tauc : ℤ := 23949621038340868125
def Nmomc : List ℤ :=
  [30, 154, 8]
end B6_6
end Sendov


