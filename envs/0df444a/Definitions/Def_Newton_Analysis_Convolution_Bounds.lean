-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_Bounds
-- name    : Newton_Analysis_Convolution_Bounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:42:59.148188+00:00
-- url     : https://prove2.me/theorems/998c76de-aecf-4454-b079-9d60a378d5e4
-- title:
--   Bounds
-- statement:
--   Definitions and structural lemmas for Bounds, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
namespace Newton
variable {n : ℕ}
end Newton


