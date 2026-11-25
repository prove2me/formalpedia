-- Prove2me | Definitions.Def_SourceProof_d5e0692f6e3d9a9902fd804f
-- name    : SourceProof_d5e0692f6e3d9a9902fd804f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:54:38.172368+00:00
-- url     : https://prove2.me/theorems/49e8a4f8-15d0-51dc-a95c-5465e9fc4f37
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.uniformIntegrable_upperApprox_value

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9

open private upperApprox_value_ae_eq_condExp from Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Bounded optional sampling in continuous time

Upper countable-range stopping times are capped at the deterministic bound.
Their values are conditional expectations of one integrable terminal value,
so they are uniformly integrable. Right continuity yields the almost-sure
limit, and Vitali gives L1 convergence. No bounded-path assumption is used.

The core statement assumes progressive measurability and common-event right
continuity. An everywhere-right-continuous adapted martingale has the former
property by the existing ProcessCore theorem. Transport from an AE regular
version under a usual filtration is kept separate.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_d5e0692f6e3d9a9902fd804f (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    UniformIntegrable (fun n ω ↦ X (τ.upperApprox T n ω) ω) 1 P :=
  ((hX.integrable T).uniformIntegrable_condExp
    (fun n ↦ (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 (τ.upperApprox T n)))).ae_eq
      (fun n ↦ (upperApprox_value_ae_eq_condExp hX τ T n).symm)
end MeasureTheory.Martingale


