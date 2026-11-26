-- Prove2me | Definitions.Def_SourceProof_27187552e7c655b929fb6618
-- name    : SourceProof_27187552e7c655b929fb6618
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:26:36.460136+00:00
-- url     : https://prove2.me/theorems/0d91d95d-e3c1-456a-ac41-94e7905a36bc
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_zero_of_finiteVariation

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_996b5538f02fe4ec38c5a73c
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.26: raw quadratic variation on finite-variation paths

The actual jump series is obtained from Stieltjes component integrals. The
path-local assertion does not require the FV event to have full measure.
The initial square and all positive-time endpoint jumps are retained.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_27187552e7c655b929fb6618
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.continuousQuadraticVariation hF) 0 P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_996b5538f02fe4ec38c5a73c hX) hF, hv]
    with ω h hvω
  exact h hvω
end IsSemimartingale

end ProbabilityTheory


