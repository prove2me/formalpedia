-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:51.266441+00:00
-- url     : https://prove2.me/theorems/47ccb877-e31b-42df-85cc-a4b89d63fb7b
-- title:
--   Arzela Ascoli
-- statement:
--   Definitions and structural lemmas for Arzela Ascoli, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
local instance instMeasurableSpaceEL2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessArzelaAscoli : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessArzelaAscoli : MeasurableNeg E := by
  infer_instance
attribute [local instance] instMeasurableSpaceEL2CompactnessArzelaAscoli instBorelSpaceEL2CompactnessArzelaAscoli instOpensMeasurableSpaceEL2CompactnessArzelaAscoli instMeasurableAddEL2CompactnessArzelaAscoli instMeasurableNegEL2CompactnessArzelaAscoli
variable {K : Set E} {ψ : E → ℝ}
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


