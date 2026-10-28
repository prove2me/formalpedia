-- Prove2me | Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
-- name    : MarkovProcess_Continuity_DenseTimeContinuousExtension
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:41:10.096353+00:00
-- url     : https://prove2.me/theorems/951bf122-2fcf-413c-9f07-80d4929de700
-- title:
--   MarkovProcess definitions: Continuity.DenseTimeContinuousExtension
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.DenseTimeContinuousExtension`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DenseTimeContinuousExtension.lean#L1-L116

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Restriction of a continuous path to the fixed dense time carrier. -/
def denseRestriction (omega : ContinuousPath alpha) : DenseTime → alpha :=
  fun q ↦ omega (DenseTime.castOrderEmbedding q)



/-- The nonnegative rational times are dense in nonnegative real time. -/
theorem denseRange_castOrderEmbedding : DenseRange DenseTime.castOrderEmbedding := by
  rw [DenseRange]
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  exact ⟨DenseTime.castOrderEmbedding q, ⟨q, rfl⟩, haq, hqb⟩

/-- A continuous path is determined by its values at the dense times. -/
theorem denseRestriction_injective [T2Space alpha] :
    Function.Injective (denseRestriction (alpha := alpha)) := by
  intro omega eta h
  apply ContinuousMap.ext
  have heq : (omega : NNReal → alpha) = eta :=
    denseRange_castOrderEmbedding.equalizer omega.continuous eta.continuous h
  exact congrFun heq

/-- A total extension, equal to the inverse on the restriction range and arbitrarily equal to
`default` away from that range. -/
def continuousExtension (default : ContinuousPath alpha) :
    (DenseTime → alpha) → ContinuousPath alpha :=
  Function.extend denseRestriction id (fun _ ↦ default)







section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- Dense-time restriction is coordinatewise Borel measurable. -/
theorem measurable_denseRestriction : Measurable (denseRestriction (alpha := alpha)) := by
  rw [measurable_pi_iff]
  intro q
  exact
    (continuous_eval (alpha := alpha) (DenseTime.castOrderEmbedding q)).borel_measurable.mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Dense-time restriction is a measurable embedding. -/
theorem measurableEmbedding_denseRestriction :
    MeasurableEmbedding (denseRestriction (alpha := alpha)) :=
  measurable_denseRestriction.measurableEmbedding denseRestriction_injective



/-- The total extension is measurable; away from the measurable restriction range its value is
the arbitrary path `default`. -/
theorem measurable_continuousExtension (default : ContinuousPath alpha) :
    Measurable (continuousExtension (alpha := alpha) default) :=
  measurableEmbedding_denseRestriction.measurable_extend measurable_id measurable_const

end Measurable
end ContinuousPath
end
end MarkovProcess


