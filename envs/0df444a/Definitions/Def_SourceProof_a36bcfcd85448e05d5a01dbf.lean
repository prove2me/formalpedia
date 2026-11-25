-- Prove2me | Definitions.Def_SourceProof_a36bcfcd85448e05d5a01dbf
-- name    : SourceProof_a36bcfcd85448e05d5a01dbf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:21.263797+00:00
-- url     : https://prove2.me/theorems/35f1ddbc-2de1-5506-932e-bcfc7a8af94b
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.finiteRestriction_represents_finiteRestrictionLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F023
import Definitions.Def_SourceProof_594405e958b8c344babc33a9
import Definitions.Def_SourceProof_f1697f4dd8137e86eb913166

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_a36bcfcd85448e05d5a01dbf (η : LevyTriplet) (n : ℕ) :
    (η.finiteRestriction n).Represents (η.finiteRestrictionLaw n) := by
  letI : IsFiniteMeasure (η.finiteRestriction n).jumpMeasure :=
    (_root_.Prove2MeSourceProof.h_594405e958b8c344babc33a9 η) n
  exact _root_.Prove2MeSourceProof.h_f1697f4dd8137e86eb913166 (η.finiteRestriction n)
end LevyTriplet

end ProbabilityTheory


