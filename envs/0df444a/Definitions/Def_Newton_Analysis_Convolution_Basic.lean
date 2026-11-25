-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_Basic
-- name    : Newton_Analysis_Convolution_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:22.52055+00:00
-- url     : https://prove2.me/theorems/de9b935c-034c-45bf-ac71-03a0f9accae9
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Basic.lean

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
namespace Newton
variable {n : ℕ}
end Newton


