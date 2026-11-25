-- Prove2me | Definitions.Def_SourceProof_c73060eb85da9035497d5cd7
-- name    : SourceProof_c73060eb85da9035497d5cd7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:32:22.934355+00:00
-- url     : https://prove2.me/theorems/9919f2dd-9a46-5a24-b95b-3cac90c66016
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.Represents.unique

import Definitions.Def_SourceProof_1a692c64413256141ec63577
import Definitions.Def_SourceProof_b069344bde66c0f8cf634bbf

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

namespace Represents
theorem _root_.Prove2MeSourceProof.h_c73060eb85da9035497d5cd7 {η ξ : LevyTriplet}
    {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ) (hξ : ξ.Represents μ) : η = ξ :=
  _root_.Prove2MeSourceProof.h_1a692c64413256141ec63577 ((_root_.Prove2MeSourceProof.h_b069344bde66c0f8cf634bbf hη) hξ)
end Represents

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


