-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:41:03.198147+00:00
-- url     : https://prove2.me/theorems/376d3f75-d589-41aa-933c-968534f96b31
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceEL2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTransfer : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessTransfer : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessTransfer : MeasurableNeg E := by
  infer_instance
attribute [local instance] instMeasurableSpaceEL2CompactnessTransfer instBorelSpaceEL2CompactnessTransfer instOpensMeasurableSpaceEL2CompactnessTransfer instMeasurableAddEL2CompactnessTransfer instMeasurableNegEL2CompactnessTransfer
variable {K : Set E} {ψ : E → ℝ}
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


