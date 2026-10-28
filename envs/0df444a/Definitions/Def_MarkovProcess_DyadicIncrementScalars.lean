-- Prove2me | Definitions.Def_MarkovProcess_DyadicIncrementScalars
-- name    : MarkovProcess_DyadicIncrementScalars
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T18:01:18.8323+00:00
-- url     : https://prove2.me/theorems/1e2c3064-ad8a-493e-a983-9d1358cb4477
-- title:
--   Dyadic Kolmogorov increment decay ratio and threshold scalars
-- statement:
--   Provides three source-faithful scalar definitions in the Kolmogorov–Chentsov dyadic increment argument: the geometric ratio measuring decay of bad-event probabilities, the level-n dyadic increment threshold, and the fixed one-level threshold ratio. Their source proofs are separately imported as theorem records.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
namespace MarkovProcess
open scoped ENNReal NNReal
noncomputable def dyadicIncrementDecayRatio (p q γ : ℝ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (1 - q + p * γ)

noncomputable def dyadicIncrementThreshold (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (((2 : ℝ≥0∞) ^ n)⁻¹) ^ γ

noncomputable def dyadicIncrementThresholdRatio (γ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-γ)
end MarkovProcess


