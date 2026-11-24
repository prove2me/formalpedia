-- Prove2me | Definitions.Def_SourceProof_636c524235253bfca8198f2f
-- name    : SourceProof_636c524235253bfca8198f2f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:33.080865+00:00
-- url     : https://prove2.me/theorems/b29c3c20-1f93-4e1a-b8e5-6bdfacc1eff4
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw.convPow

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F002
import Definitions.Def_SourceProof_21f040e5ec5495fe7abf1831
import Definitions.Def_SourceProof_d332d56749c842e62ff71033

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Convolution semigroups of probability laws

The basic predicate contains only the semigroup equation.  In particular it does not silently
assert an identity law at time zero or continuity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section Topology

open TopologicalSpace

variable [TopologicalSpace G] [PseudoMetrizableSpace G] [SecondCountableTopology G]
  [BorelSpace G] [ContinuousAdd G]

end Topology

section OrderedReal

namespace IsNonnegativeLaw
theorem _root_.Prove2MeSourceProof.h_636c524235253bfca8198f2f {μ : ProbabilityMeasure ℝ}
    (hμ : IsNonnegativeLaw μ) (n : ℕ) : IsNonnegativeLaw (convPow μ n) := by
  induction n with
  | zero => simp [convPow]
  | succ n ih => exact (_root_.Prove2MeSourceProof.h_21f040e5ec5495fe7abf1831 ih) hμ
end IsNonnegativeLaw

end OrderedReal

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {T G : Type*} [Add T] [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section Continuous

variable [TopologicalSpace G] [OpensMeasurableSpace G]

section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

end Metrizable

section Real

end Real

end Continuous

end ProbabilityTheory


