-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F001
-- name    : BrownianMotion_Continuity_KolmogorovChentsovInequality_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:24:12.996712+00:00
-- url     : https://prove2.me/theorems/8eb0d6b9-24bb-4fc1-9de9-113190bf7ebe
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsovInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsovInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F001
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003
import Mathlib.Data.Set.FiniteExhaustion

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

noncomputable
-- the `max 0 ...` in the blueprint is performed by `ENNReal.ofReal` here
def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) (U : Set T) : ℝ≥0∞ :=
  2 ^ (2 * p + 5 * q + 1) * c * (Metric.ediam U + 1) ^ (q - d)
  * ∑' (k : ℕ), 2 ^ (k * (β * p - (q - d)))
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 2) * d)) ^ q + Cp d p q)
end PseudoEMetricSpace

end ProbabilityTheory


