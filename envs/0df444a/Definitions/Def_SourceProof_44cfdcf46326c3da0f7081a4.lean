-- Prove2me | Definitions.Def_SourceProof_44cfdcf46326c3da0f7081a4
-- name    : SourceProof_44cfdcf46326c3da0f7081a4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:00:39.404556+00:00
-- url     : https://prove2.me/theorems/70a3af48-9ead-4a96-bec9-2422975687d6
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.map_finsetSum_gaussianReal
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A finite sum of independent centred Gaussians

Adding one summand at a time, using that the sum of two independent Gaussians is Gaussian with
the sum of the variances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_44cfdcf46326c3da0f7081a4 {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {v : ι → ℝ≥0}
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [gaussianReal_zero_var, Measure.map_const, measure_univ, one_smul]
  | insert a s ha ih =>
      have hfun : (fun ω => ∑ i ∈ insert a s, X i ω)
          = (fun ω => ∑ i ∈ s, X i ω) + X a := by
        funext ω
        simp only [Pi.add_apply, Finset.sum_insert ha]
        ring
      have hpi : (fun ω => ∑ i ∈ s, X i ω) = ∑ j ∈ s, X j := by
        funext ω; rw [Finset.sum_apply]
      have hindep : IndepFun (fun ω => ∑ i ∈ s, X i ω) (X a) P := by
        rw [hpi]; exact hind.indepFun_finsetSum_of_notMem hX ha
      rw [hfun, Finset.sum_insert ha,
        gaussianReal_add_gaussianReal_of_indepFun hindep ih (hlaw a), add_zero, add_comm]
end LevyStochCalc.Probability


