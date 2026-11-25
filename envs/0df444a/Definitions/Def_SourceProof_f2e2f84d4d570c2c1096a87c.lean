-- Prove2me | Definitions.Def_SourceProof_f2e2f84d4d570c2c1096a87c
-- name    : SourceProof_f2e2f84d4d570c2c1096a87c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:10.175859+00:00
-- url     : https://prove2.me/theorems/4b31667d-b8e8-42e7-bd24-79015985cd22
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integrable_quadraticVariationSum_real

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_dc59e39708930ceeee4c5f5a
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Poisson square-increment sums converge to the actual count

For every finite partition, the square sum exceeds the count and its mean
excess is exactly `rate^2 * sum gap^2`. Thus arbitrary vanishing meshes give
L1 and probability convergence, without assuming unit jumps or a bracket.
-/

@[expose] public section

open MeasureTheory Filter Finset StochLean
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate T : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_f2e2f84d4d570c2c1096a87c
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    Integrable (fun ω ↦ quadraticVariationSum π (fun s ↦ (N s ω : ℝ))) P := by
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (_root_.Prove2MeSourceProof.h_dc59e39708930ceeee4c5f5a hN) ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
end IsPoissonProcess

end ProbabilityTheory


