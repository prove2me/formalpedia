-- Prove2me | Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
-- name    : StochLean_Probability_Process_LocalMartingale_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:34.903889+00:00
-- url     : https://prove2.me/theorems/846f49a7-0d3a-4e6b-bfe2-18d6fdeef634
-- title:
--   StochLean: Probability.Process.LocalMartingale F001

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_834b246e9dd55f8ec980992d
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter local martingales and Klenke localization

The canonical local martingale uses masked stopped UI martingales (Protter I.6).
Klenke's unmasked localizer is witness data, not a competing process hierarchy.
The unmasked bridge requires integrability of the initial value. Time is `ℝ≥0`;
stopping times have values in `WithTop ℝ≥0`, and stopped processes are only
evaluated at finite deterministic times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem martingale_indicator_initial (hX : Martingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Martingale (fun t ↦ s.indicator (X t)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted t).indicator (F.mono bot_le s hs), ?_⟩
  intro s' t hst
  refine (condExp_indicator (hX.integrable t) (F.mono bot_le s hs)).trans ?_
  filter_upwards [hX.condExp_ae_eq hst] with ω hω
  by_cases h : ω ∈ s <;> simp [h, hω]
end ProbabilityTheory


