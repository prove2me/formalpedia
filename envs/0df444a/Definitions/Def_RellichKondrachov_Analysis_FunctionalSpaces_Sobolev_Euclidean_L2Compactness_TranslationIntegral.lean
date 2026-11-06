-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:06.392468+00:00
-- url     : https://prove2.me/theorems/d717afdc-afe2-4cf2-9b3d-0edadc096d82
-- title:
--   Translation Integral
-- statement:
--   Definitions and structural lemmas for Translation Integral, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceEL2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddEL2CompactnessTranslationIntegral : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessTranslationIntegral : MeasurableNeg E := by
  infer_instance
attribute [local instance] instMeasurableSpaceEL2CompactnessTranslationIntegral instBorelSpaceEL2CompactnessTranslationIntegral instOpensMeasurableSpaceEL2CompactnessTranslationIntegral instMeasurableAddEL2CompactnessTranslationIntegral instMeasurableNegEL2CompactnessTranslationIntegral
variable {ψ : E → ℝ}
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


