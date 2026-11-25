-- Prove2me | Definitions.Def_SourceProof_c665a2779da0472ba911a85d
-- name    : SourceProof_c665a2779da0472ba911a85d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:38.096167+00:00
-- url     : https://prove2.me/theorems/34181da9-c7a7-4787-a486-893f4d415a78
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_SourceProof_bbf2dce0c119b003681db438
import Definitions.Def_SourceProof_c1502d54d2b7490012bf0be0
import Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078
import Definitions.Def_SourceProof_f354c3aa1b2bfac52fcde7e4

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

@[simp] theorem _root_.Prove2MeSourceProof.h_c665a2779da0472ba911a85d (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) : (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F).elementaryIntegral X = 0 := by
  rw [_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 _ (ProbabilityTheory.SimplePredictableRep.zero F)
    (_root_.Prove2MeSourceProof.h_bbf2dce0c119b003681db438 F), _root_.Prove2MeSourceProof.h_f354c3aa1b2bfac52fcde7e4]
end IsSimplePredictable
end ProbabilityTheory


