-- Prove2me | Definitions.Def_SourceProof_28b29a6700445f0b3c267011
-- name    : SourceProof_28b29a6700445f0b3c267011
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:02:45.965882+00:00
-- url     : https://prove2.me/theorems/78ac65cf-2e98-566d-af5a-a4a4a3aadfbf
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.measurable_integral

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the source elementary integral

Finite stopping endpoints are evaluated using the existing usual-filtration path-version
theorem. Integrator integrability and bounds on the integrand are not needed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_28b29a6700445f0b3c267011 (H : SimplePredictableRep F)
    (hX : Adapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Measurable (H.integral X) := by
  have hm (τ : ProbabilityTheory.FiniteStoppingTime F) : Measurable (fun ω ↦ X (τ ω) ω) :=
    ((_root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0 hX.stronglyAdapted) hF hr τ.isStoppingTime).mono
      (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 τ) le_rfl
  apply ((H.measurable_initial.mono (F.le 0) le_rfl).mul
    ((hX 0).mono (F.le 0) le_rfl)).add
  exact Finset.measurable_fun_sum univ fun i _ ↦
    ((H.measurable_coefficient i).mono (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 (H.partition.point i.castSucc)) le_rfl).mul
      ((hm _).sub (hm _))
end SimplePredictableRep

end ProbabilityTheory


