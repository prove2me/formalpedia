-- Prove2me | Definitions.Def_SourceProof_d72fb9e89be890a633fb10d1
-- name    : SourceProof_d72fb9e89be890a633fb10d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:02:45.28107+00:00
-- url     : https://prove2.me/theorems/832411e1-e4ed-5dcf-8e48-36d539ee4325
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.tendsto_charFun_finiteRestrictionLaw

import Definitions.Def_SourceProof_31684b00a50318d07e4b5834
import Definitions.Def_SourceProof_a36bcfcd85448e05d5a01dbf

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


theorem _root_.Prove2MeSourceProof.h_d72fb9e89be890a633fb10d1 (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n ↦ charFun (η.finiteRestrictionLaw n : Measure ℝ) t) Filter.atTop
      (nhds (Complex.exp (η.exponent t))) := by
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp
    ((_root_.Prove2MeSourceProof.h_31684b00a50318d07e4b5834 η) t)
  have heq : (fun n ↦ charFun (η.finiteRestrictionLaw n : Measure ℝ) t) =
      (fun n ↦ Complex.exp ((η.finiteRestriction n).exponent t)) := by
    funext n
    exact (_root_.Prove2MeSourceProof.h_a36bcfcd85448e05d5a01dbf η) n t
  rw [heq]
  exact hexp
end LevyTriplet

end ProbabilityTheory


