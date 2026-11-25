-- Prove2me | Definitions.Def_SourceProof_cfcbcbe0a1d572b37d51f9a8
-- name    : SourceProof_cfcbcbe0a1d572b37d51f9a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:23:34.997406+00:00
-- url     : https://prove2.me/theorems/42a5939a-db25-4d8b-8ead-5aebfa098ddc
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.isSemimartingale_compensated

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_3371ea3822340c17baa8afad
import Definitions.Def_SourceProof_de21bad3305347f56350145d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The compensated Poisson martingale for an explicit filtration

The process is the actual real count minus its rate times time. Independent
future increments from the chosen past are explicit, so the theorem does not
assert a false martingale property for arbitrary enlarged filtrations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_cfcbcbe0a1d572b37d51f9a8
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    IsSemimartingale (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) F P := by
  apply (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f (_root_.Prove2MeSourceProof.h_de21bad3305347f56350145d hN)) _ hF (_root_.Prove2MeSourceProof.h_3371ea3822340c17baa8afad hN)
  intro t
  exact ((continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp
    (ha t)).sub measurable_const
end IsPoissonProcess

end ProbabilityTheory


