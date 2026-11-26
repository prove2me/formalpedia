-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree10_11
-- name    : Sendov_FiniteRange_Degree10_11
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:04:55.788909+00:00
-- url     : https://prove2.me/theorems/aa9ee319-0573-4f11-a1d3-02e32ddf9655
-- title:
--   Degree10 11
-- statement:
--   Definitions and structural lemmas for Degree10 11, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B10_11
def Lc : ℤ := 2520
def betac : ℤ := 82590802561
def tauc : ℤ := 484002949944962611058313401081496854475499965300896802417388157646295122586173254149900368313668004057389423899346929
def Nmomc : List ℤ :=
  [472392, 1312200, 1971216, 3407184, 294192, 12096, 192]
end B10_11
end Sendov


