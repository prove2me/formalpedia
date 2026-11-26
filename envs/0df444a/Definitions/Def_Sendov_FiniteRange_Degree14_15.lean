-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree14_15
-- name    : Sendov_FiniteRange_Degree14_15
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:05:50.173896+00:00
-- url     : https://prove2.me/theorems/45b2d5ac-42fd-4266-9ea8-d61557f57fd8
-- title:
--   Degree14 15
-- statement:
--   Definitions and structural lemmas for Degree14 15, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B14_15
def Lc : ℤ := 360360
def betac : ℤ := 5273811281588129281
def tauc : ℤ := 5240604256749137818001775409217258559398270598665938104246888891334041344492138378350247489747112270657502763060533670335383336131627922353242397074581977699087266735169689253384888787652968648421800644465440084079049341105429958677566179709215175220574978194512241977108241372511737172688952893630525928871748289
def Nmomc : List ℤ :=
  [259845693120, 782498283840, 1107091851840, 1019339156160, 768295987680, 853275774240, 79511527040, 4444832000, 147210240, 2670080, 20480]
end B14_15
end Sendov


