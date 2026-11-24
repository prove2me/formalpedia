-- Prove2me | Definitions.Def_StochLean_Probability_Process_Poisson_IntervalAxioms_F000
-- name    : StochLean_Probability_Process_Poisson_IntervalAxioms_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:13.370836+00:00
-- url     : https://prove2.me/theorems/24493789-ea3f-4fe6-a3b8-0ef018b53e77
-- title:
--   StochLean: Probability.Process.Poisson.IntervalAxioms F000

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Mathlib.Analysis.Calculus.Deriv.Slope

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Interval-count axioms for Poisson processes

This file formalizes Klenke's interval axioms P1--P5 for a counting process.  In addition to
those axioms, the predicate records the design-level path convention used by StochLean: paths are
almost surely monotone and right-continuous on one common event, and the process starts at zero.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The number of events in the half-open time interval `(s, t]`.  Statements about this count
carry the hypothesis `s ≤ t`, so natural subtraction is genuine count subtraction. -/
def poissonIntervalCount (X : NNReal → Ω → ℕ) (s t : NNReal) (ω : Ω) : ℕ :=
  X t ω - X s ω
/-- Klenke's P1--P5 interval-count axioms, together with the corrected path semantics fixed by
the StochLean design: one common almost-sure event supports monotone right-continuous paths. -/
structure SatisfiesPoissonIntervalAxioms (X : NNReal → Ω → ℕ)
    (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] : Prop where
  aemeasurable : ∀ t, AEMeasurable (X t) P
  initial : X 0 =ᵐ[P] fun _ ↦ 0
  monotonePaths : HasMonotonePaths X P
  rightContinuousPaths : HasRightContinuousPaths X P
  /-- P1: adjacent interval counts add. -/
  intervalAdditive : ∀ r s t, r ≤ s → s ≤ t →
    poissonIntervalCount X r t =ᵐ[P] fun ω ↦
      poissonIntervalCount X r s ω + poissonIntervalCount X s t ω
  /-- P2: the law of an interval count depends only on its length. -/
  stationaryIntervalLaw : ∀ r s t u, r ≤ s → t ≤ u → s - r = u - t →
    IdentDistrib (poissonIntervalCount X r s) (poissonIntervalCount X t u) P P
  /-- P3: counts on successive disjoint intervals are independent. -/
  indepIncrements : HasIndepIncrements X P
  /-- P4: every bounded interval has a finite first moment. -/
  finiteMean : ∀ s t, s ≤ t →
    Integrable (fun ω ↦ (poissonIntervalCount X s t ω : ℝ)) P
  /-- P5: the probability of two or more events in an interval of length `ε` is `o(ε)`.
  This is stated in Klenke's exact `limsup` form. -/
  rareMultipleJump :
    limsup (fun ε : ℝ ↦
      P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε)
      (𝓝[>] 0) = 0
namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

end IsPoissonProcess

end ProbabilityTheory


