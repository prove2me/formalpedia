-- Prove2me | Definitions.Def_SourceProof_1afe17b1cfdd6bcd7a6b3c52
-- name    : SourceProof_1afe17b1cfdd6bcd7a6b3c52
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:58.065944+00:00
-- url     : https://prove2.me/theorems/409aadd2-db82-40d2-89d2-05b23d3fc1bd
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_affine

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F018
import Definitions.Def_SourceProof_b515f0f75ab82bfa805e8d71
import Definitions.Def_SourceProof_c3b700cf3e07c09b0f6a6eee
import Definitions.Def_SourceProof_c59b662aa91c3d86c96a92b3
import Definitions.Def_SourceProof_f9b33963924eb7ac5401881f

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


theorem _root_.Prove2MeSourceProof.h_1afe17b1cfdd6bcd7a6b3c52 (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) (t : ℝ) :
    (η.affine a d ha).exponent t =
      η.exponent (a * t) + ((d * t : ℝ) : ℂ) * Complex.I := by
  have hmap :
      (∫ x, ProbabilityTheory.levyExponentIntegrand t x ∂(η.jumpMeasure.map fun x => a * x)) =
        ∫ x, ProbabilityTheory.levyExponentIntegrand t (a * x) ∂η.jumpMeasure := by
    rw [integral_map (by fun_prop)
      (_root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f t).aestronglyMeasurable]
  have hcorr := (_root_.Prove2MeSourceProof.h_c59b662aa91c3d86c96a92b3 η.isLevyMeasure_jumpMeasure) ha
  have hexp := (_root_.Prove2MeSourceProof.h_c3b700cf3e07c09b0f6a6eee η.isLevyMeasure_jumpMeasure) (a * t)
  have hcorrC : Integrable
      (fun x => (((t * ProbabilityTheory.affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) η.jumpMeasure :=
    ((hcorr.const_mul t).ofReal.mul_const Complex.I)
  have hcast :
      (∫ x, ((t * ProbabilityTheory.affineDriftIntegrand a x : ℝ) : ℂ) ∂η.jumpMeasure) =
        ((∫ x, t * ProbabilityTheory.affineDriftIntegrand a x ∂η.jumpMeasure : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * ProbabilityTheory.affineDriftIntegrand a x ∂η.jumpMeasure) =
        t * ∫ x, ProbabilityTheory.affineDriftIntegrand a x ∂η.jumpMeasure :=
    integral_const_mul _ _
  simp only [ProbabilityTheory.LevyTriplet.exponent, ProbabilityTheory.LevyTriplet.affine]
  rw [hmap]
  rw [show (fun x => ProbabilityTheory.levyExponentIntegrand t (a * x)) =
      (fun x => ProbabilityTheory.levyExponentIntegrand (a * t) x -
        (((t * ProbabilityTheory.affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) by
    funext x
    exact _root_.Prove2MeSourceProof.h_b515f0f75ab82bfa805e8d71 a t x]
  rw [integral_sub hexp hcorrC]
  rw [integral_mul_const, hcast, hreal]
  simp only [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ ha.le]
  simp only [Complex.ofReal_mul]
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


