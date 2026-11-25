-- Prove2me | Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
-- name    : Newton_MeasureTheory_Function_LpSpace_Duality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:42.457116+00:00
-- url     : https://prove2.me/theorems/47284d3e-7138-49d8-86e9-ec47117b04cc
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
namespace Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end Newton


