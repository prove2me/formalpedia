-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_Auxiliary
-- name    : Newton_Analysis_Convolution_Auxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:40.957807+00:00
-- url     : https://prove2.me/theorems/d77d0acb-ac29-48e9-9904-9dc2f3e2f235
-- title:
--   Auxiliary
-- statement:
--   Definitions and structural lemmas for Auxiliary, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
namespace Newton
variable {n : ℕ}
end Newton


