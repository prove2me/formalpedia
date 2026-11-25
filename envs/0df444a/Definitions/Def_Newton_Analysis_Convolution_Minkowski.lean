-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_Minkowski
-- name    : Newton_Analysis_Convolution_Minkowski
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:30.321223+00:00
-- url     : https://prove2.me/theorems/02667893-d94e-4045-acf5-554e1b2a539d
-- title:
--   Minkowski
-- statement:
--   Definitions and structural lemmas for Minkowski, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
namespace Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
section MinkowskiGeneral
variable [SFinite μ] [SFinite ν]
end MinkowskiGeneral
section ConvolutionPreparatory
variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]
end ConvolutionPreparatory
end Newton


