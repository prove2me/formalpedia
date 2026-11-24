-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:31.907804+00:00
-- url     : https://prove2.me/theorems/326aeb2a-6773-4775-b9bc-1c63a690e935
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable F000

import Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter simple predictable processes and their elementary integral

The coefficients are finite real random variables, measurable at the left
stopping endpoint. They need not be bounded. A representation is witness data;
the public process is a raw function. Representation independence is proved
before the public integral selector is introduced.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure SimplePredictableRep (F : Filtration ℝ≥0 mΩ) where
  partition : StoppingTimePartition F
  initial : Ω → ℝ
  measurable_initial : Measurable[F 0] initial
  coefficient : Fin partition.size → Ω → ℝ
  measurable_coefficient : ∀ i, Measurable[(partition.point i.castSucc).measurableSpace]
    (coefficient i)
namespace SimplePredictableRep

variable {F : Filtration ℝ≥0 mΩ}

noncomputable def toProcess (H : SimplePredictableRep F) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if t = 0 then H.initial ω else
    ∑ i, if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then H.coefficient i ω else 0
/-- Finite-sum integral on representation data. -/
def integral (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  H.initial ω * X 0 ω + ∑ i, H.coefficient i ω *
    (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω)
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


