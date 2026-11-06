-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:41.785688+00:00
-- url     : https://prove2.me/theorems/20aaa80b-f88a-4587-a5c7-04e5fd9fa38d
-- title:
--   Translation Estimate H1
-- statement:
--   Definitions and structural lemmas for Translation Estimate H1, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
import Mathlib.Topology.Order.OrderClosed
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance instMeasurableSpaceTranslationEstimateH1 :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimateH1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimateH1 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslationEstimateH1 : MeasurableAdd E := by
  infer_instance
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
end
end
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


