-- Prove2me | Definitions.Def_SourceProof_ad0628f973de439b357972c1
-- name    : SourceProof_ad0628f973de439b357972c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:42:05.194912+00:00
-- url     : https://prove2.me/theorems/4dc0dd20-f773-4ffe-b73c-6479361877dc
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.charFun_weightedJumpMeasure

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
import Definitions.Def_SourceProof_1c883159017bdf91b31257ab
import Definitions.Def_SourceProof_f62a285e39f3cce92855751f
import Definitions.Def_SourceProof_fdf18211a3aef3d14d3220f0

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

theorem _root_.Prove2MeSourceProof.h_ad0628f973de439b357972c1 (η : LevyTriplet) (s t : ℝ) :
    charFun (weightedJumpMeasure η s) t =
      -((∫ x, levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        (∫ x, levyExponentIntegrand (t - s) x ∂η.jumpMeasure) -
        2 * ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  rw [charFun_apply_real, ProbabilityTheory.LevyTriplet.weightedJumpMeasure,
    integral_withDensity_eq_integral_smul (_root_.Prove2MeSourceProof.h_1c883159017bdf91b31257ab s)]
  rw [integral_congr_ae (ae_of_all _ fun x => by
    simpa only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul] using
      _root_.Prove2MeSourceProof.h_fdf18211a3aef3d14d3220f0 s t x)]
  rw [integral_neg]
  have hp := (_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) (t + s)
  have hm := (_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) (t - s)
  have ht := (_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) t
  congr 1
  have hsub := integral_sub (hp.add hm) (ht.const_mul 2)
  have hadd := integral_add hp hm
  have hadd' : integral η.jumpMeasure
      (ProbabilityTheory.levyExponentIntegrand (t + s) + ProbabilityTheory.levyExponentIntegrand (t - s)) =
      (∫ x, ProbabilityTheory.levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        ∫ x, ProbabilityTheory.levyExponentIntegrand (t - s) x ∂η.jumpMeasure := by
    rw [show ProbabilityTheory.levyExponentIntegrand (t + s) + ProbabilityTheory.levyExponentIntegrand (t - s) =
      (fun x => ProbabilityTheory.levyExponentIntegrand (t + s) x +
        ProbabilityTheory.levyExponentIntegrand (t - s) x) by rfl]
    exact hadd
  have hmul : (∫ x, 2 * ProbabilityTheory.levyExponentIntegrand t x ∂η.jumpMeasure) =
      2 * ∫ x, ProbabilityTheory.levyExponentIntegrand t x ∂η.jumpMeasure :=
    integral_const_mul 2 (ProbabilityTheory.levyExponentIntegrand t)
  exact hsub.trans (by rw [hadd', hmul])
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


