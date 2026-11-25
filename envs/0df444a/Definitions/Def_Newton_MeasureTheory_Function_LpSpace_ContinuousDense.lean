-- Prove2me | Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
-- name    : Newton_MeasureTheory_Function_LpSpace_ContinuousDense
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:07.083058+00:00
-- url     : https://prove2.me/theorems/fa1a73d2-be5b-4dc5-9bd8-e03276edc5db
-- title:
--   Continuous Dense
-- statement:
--   Definitions and structural lemmas for Continuous Dense, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
namespace Newton
variable {n : ℕ}
end Newton


