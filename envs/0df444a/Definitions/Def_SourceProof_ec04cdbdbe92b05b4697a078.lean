-- Prove2me | Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078
-- name    : SourceProof_ec04cdbdbe92b05b4697a078
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:58:43.868207+00:00
-- url     : https://prove2.me/theorems/c9219c6c-34f9-439a-a2f7-55dba811cd91
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_eq

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb

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

end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 (hH : IsSimplePredictable H F)
    (R : SimplePredictableRep F) (hR : R.toProcess = H) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral X = R.integral X :=
  (_root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb hH.choose) R (hH.choose_spec.trans hR.symm) X
end IsSimplePredictable
end ProbabilityTheory


