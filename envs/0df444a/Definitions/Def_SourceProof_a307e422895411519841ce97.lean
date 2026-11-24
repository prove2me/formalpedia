-- Prove2me | Definitions.Def_SourceProof_a307e422895411519841ce97
-- name    : SourceProof_a307e422895411519841ce97
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:25.314191+00:00
-- url     : https://prove2.me/theorems/afcb97cf-a681-44a3-962a-e2e6f6fd162a
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.comp

import Definitions.Def_StochLean_Probability_Process_UCP_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_a307e422895411519841ce97 {ι κ : Type*} {X : ι → ℝ≥0 → Ω → ℝ}
    {l : Filter ι} {v : Filter κ} {s : κ → ι}
    (hX : TendstoUCP P X l Y) (hs : Tendsto s v l) :
    TendstoUCP P (X ∘ s) v Y := fun T ε hε ↦ (hX T ε hε).comp hs
end TendstoUCP

end ProbabilityTheory


