-- Prove2me | Definitions.Def_SourceProof_1a692c64413256141ec63577
-- name    : SourceProof_1a692c64413256141ec63577
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:27.523969+00:00
-- url     : https://prove2.me/theorems/0e8e91ea-0c56-50d3-be9e-4f738fd613af
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.eq_of_exponent_eq

import Definitions.Def_SourceProof_01243bc92c93469b6f708225
import Definitions.Def_SourceProof_96e4a2723d12915db081936e
import Definitions.Def_SourceProof_daf4430892484ad2f4cc58ba

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

theorem _root_.Prove2MeSourceProof.h_1a692c64413256141ec63577 {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) : η = ξ := by
  rw [LevyTriplet.mk.injEq]
  exact ⟨_root_.Prove2MeSourceProof.h_96e4a2723d12915db081936e h, _root_.Prove2MeSourceProof.h_daf4430892484ad2f4cc58ba h,
    _root_.Prove2MeSourceProof.h_01243bc92c93469b6f708225 h⟩
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


