-- Prove2me | Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
-- name    : StochLean_Probability_Process_LocalMartingale_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:03.73247+00:00
-- url     : https://prove2.me/theorems/f44cd63d-cf74-43ae-bbd1-076b75ac73cc
-- title:
--   StochLean: Probability.Process.LocalMartingale F000

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

/-- Deterministic-time UI, in addition to the canonical Mathlib martingale predicate.
This is not the stopping-time Class D predicate. -/
def IsUIMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Martingale X F P ∧ UniformIntegrable X 1 P
/-- Protter I.6 reducing time: the unmasked stopped process is a UI martingale.
The fundamental sequence instead reduces the masked process. -/
def IsReducingStoppingTime (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime F τ ∧ IsUIMartingale (stoppedProcess X τ) F P
/-- A monotone sequence of reducing times tending to infinity almost surely. -/
def IsFundamentalSequence (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : ℕ → Ω → WithTop ℝ≥0) : Prop :=
  IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
    ∀ n, IsUIMartingale
      (stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)) F P
/-- Canonical Protter local martingale. Path regularity holds on one common event. -/
def IsLocalMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧ ∃ τ, IsFundamentalSequence X F P τ
def IsContinuousLocalMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsLocalMartingale X F P ∧ HasContinuousPaths X P
/-- Klenke 21.66 source witness: stopped processes are unmasked UI martingales. -/
def IsKlenkeLocalizingSequence (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (τ : ℕ → Ω → WithTop ℝ≥0) : Prop :=
  IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
    ∀ n, IsUIMartingale (stoppedProcess X (τ n)) F P
/-- CM-SQ-REF01: finite-time square integrability, with no global L2 bound. -/
def IsSquareIntegrableMartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Martingale X F P ∧ ∀ t, MemLp (X t) 2 P
end ProbabilityTheory


