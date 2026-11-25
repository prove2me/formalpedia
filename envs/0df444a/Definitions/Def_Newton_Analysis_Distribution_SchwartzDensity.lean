-- Prove2me | Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity
-- name    : Newton_Analysis_Distribution_SchwartzDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:47:30.637738+00:00
-- url     : https://prove2.me/theorems/331e31e6-66a9-459c-8781-7f9f8d4d6bb9
-- title:
--   Schwartz Density
-- statement:
--   Definitions and structural lemmas for Schwartz Density, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
namespace Newton
variable {n : ℕ}
end Newton


