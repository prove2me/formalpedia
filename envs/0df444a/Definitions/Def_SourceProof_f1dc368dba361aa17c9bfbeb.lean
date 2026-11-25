-- Prove2me | Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb
-- name    : SourceProof_f1dc368dba361aa17c9bfbeb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:40.998562+00:00
-- url     : https://prove2.me/theorems/599a9bae-d51e-48fe-b711-c07804609238
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F000
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_f663a9831488630e6f3e2684
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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

namespace SimplePredictableRep

variable {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb (H K : SimplePredictableRep F) (hHK : H.toProcess = K.toProcess)
    (X : ℝ≥0 → Ω → ℝ) : H.integral X = K.integral X := by
  funext ω
  have hinit : H.initial ω = K.initial ω := by
    simpa only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417] using congrFun (congrFun hHK 0) ω
  have hsum := _root_.Prove2MeSourceProof.h_f663a9831488630e6f3e2684
    (fun i : Fin H.partition.size ↦ H.partition.point i.castSucc ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.succ ω)
    (fun i : Fin H.partition.size ↦ H.coefficient i ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.castSucc ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.succ ω)
    (fun i : Fin K.partition.size ↦ K.coefficient i ω)
    (fun i ↦ (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) i)
    (fun i ↦ (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (K.partition.path ω)) i)
    (fun t ht ↦ by
      simpa only [ProbabilityTheory.SimplePredictableRep.toProcess, ne_of_gt ht, ↓reduceIte] using congrFun (congrFun hHK t) ω)
    (fun t ↦ X t ω)
  exact congrArg₂ (· + ·) (congrArg (fun a ↦ a * X 0 ω) hinit) hsum
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


