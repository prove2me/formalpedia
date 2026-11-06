-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:42:25.197488+00:00
-- url     : https://prove2.me/theorems/ed58710e-7100-41c2-8b81-70e12b3cc659
-- title:
--   Rellich
-- statement:
--   Definitions and structural lemmas for Rellich, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
local instance instMeasurableSpaceRellich : MeasurableSpace E := borel E
local instance instBorelSpaceRellich : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceRellich : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddRellich : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegRellich : MeasurableNeg E := by
  infer_instance
local instance instFactOneLeTwoSobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL
end Volume
end
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


