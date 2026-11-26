-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree12_13
-- name    : Sendov_FiniteRange_Degree12_13
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:05:13.941867+00:00
-- url     : https://prove2.me/theorems/37b1f72e-b85e-556e-b395-552982a533b8
-- title:
--   Degree12 13
-- statement:
--   Definitions and structural lemmas for Degree12 13, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B12_13
def Lc : ℤ := 27720
def betac : ℤ := 538941732215041
def tauc : ℤ := 6292050050870377734039180756234778163021074014036716599319294695000296491713270664825204672831809746575409998007435248501929604780211870392204795696401964180489810388769719091757577450834981070202288673
def Nmomc : List ℤ :=
  [265646304, 754389504, 1044603648, 1046977536, 1399732528, 127959680, 6424320, 167936, 1792]
end B12_13
end Sendov


