-- Prove2me | Definitions.Def_SourceProof_442eedb3cbc1d65319ef7cc0
-- name    : SourceProof_442eedb3cbc1d65319ef7cc0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:23.488297+00:00
-- url     : https://prove2.me/theorems/dd7b4cfe-6e0d-592b-b5ca-2bc48671f702
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.gaussian_represents_gaussianLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_SourceProof_3c9195c64e429293f81ae822
import Definitions.Def_SourceProof_a9754c6a2daad201e1fa7291

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

theorem _root_.Prove2MeSourceProof.h_442eedb3cbc1d65319ef7cc0 (m : ℝ) (v : ℝ≥0) :
    (gaussian m v).Represents (gaussianLaw m v) := by
  intro t
  rw [_root_.Prove2MeSourceProof.h_3c9195c64e429293f81ae822, charFun_gaussianReal, _root_.Prove2MeSourceProof.h_a9754c6a2daad201e1fa7291]
  congr 1
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


