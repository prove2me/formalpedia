-- Prove2me | Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
-- name    : MarkovProcess_Continuity_DyadicIncrements
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:37:57.522569+00:00
-- url     : https://prove2.me/theorems/2f9aae81-fee8-4512-8910-7fedff1a94f9
-- title:
--   MarkovProcess definitions: Continuity.DyadicIncrements
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.DyadicIncrements`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L1-L246

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal


/-- The geometric ratio in the dyadic Kolmogorov--Chentsov estimate. -/
noncomputable def dyadicIncrementDecayRatio (p q γ : ℝ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (1 - q + p * γ)







end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The level-`n` increment threshold used in the dyadic Kolmogorov--Chentsov argument. -/
noncomputable def dyadicIncrementThreshold (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (((2 : ℝ≥0∞) ^ n)⁻¹) ^ γ













end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal


/-- The ratio between consecutive dyadic increment thresholds. -/
noncomputable def dyadicIncrementThresholdRatio (γ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-γ)











end DyadicThresholdTail

end MarkovProcess


