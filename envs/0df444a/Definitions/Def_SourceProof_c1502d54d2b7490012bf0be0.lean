-- Prove2me | Definitions.Def_SourceProof_c1502d54d2b7490012bf0be0
-- name    : SourceProof_c1502d54d2b7490012bf0be0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:11.448442+00:00
-- url     : https://prove2.me/theorems/b8356114-18f9-40e7-bbd5-4c91223d32d1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_bbf2dce0c119b003681db438

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

theorem _root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 (F : Filtration ℝ≥0 mΩ) : IsSimplePredictable (0 : ℝ≥0 → Ω → ℝ) F :=
  ⟨ProbabilityTheory.SimplePredictableRep.zero F, _root_.Prove2MeSourceProof.h_bbf2dce0c119b003681db438 F⟩
end IsSimplePredictable
end ProbabilityTheory


