-- Prove2me | Definitions.Def_SourceProof_df666fc452357fe670b01cc3
-- name    : SourceProof_df666fc452357fe670b01cc3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:06.561267+00:00
-- url     : https://prove2.me/theorems/4e1cab1d-3b48-4a9d-b870-e5bc112a2b55
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConvolutionSemigroup.convPow_succ

import Definitions.Def_SourceProof_cce2f2b17a1ce0d26138b150
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F005
import Definitions.Def_SourceProof_636c524235253bfca8198f2f
import Definitions.Def_SourceProof_78d563fba2e0cab899d408b9
import Definitions.Def_SourceProof_ef369f12801e25b88b9d4546
import Definitions.Def_SourceProof_f7191f58deacc07c2d87f604

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Infinitely divisible probability laws

The definition is law-first: every positive convolution root must exist.  No process or path-space
realization is bundled into the predicate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

namespace IsConvolutionSemigroup
theorem _root_.Prove2MeSourceProof.h_df666fc452357fe670b01cc3
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν)
    (t : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure.convPow (ν t) (n + 1) = ν ((n + 1) • t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [_root_.Prove2MeSourceProof.h_ef369f12801e25b88b9d4546, ih, ← (_root_.Prove2MeSourceProof.h_f7191f58deacc07c2d87f604 hν)]
      congr 1
end IsConvolutionSemigroup

end ProbabilityTheory


