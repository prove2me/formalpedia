-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_InnerBound
-- name    : Newton_Analysis_Convolution_InnerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:32.670119+00:00
-- url     : https://prove2.me/theorems/800c6746-5ff4-4a2a-b792-d0e2de4d9bb3
-- title:
--   Inner Bound
-- statement:
--   Definitions and structural lemmas for Inner Bound, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/InnerBound.lean

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
namespace Newton
variable {n : ℕ}
end Newton


