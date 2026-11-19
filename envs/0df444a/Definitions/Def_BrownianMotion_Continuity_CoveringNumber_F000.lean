-- Prove2me | Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F000
-- name    : BrownianMotion_Continuity_CoveringNumber_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:13:04.889594+00:00
-- url     : https://prove2.me/theorems/c086d3ce-a72c-47d0-9e14-76c3cebb1040
-- title:
--   Source declarations: BrownianMotion.Continuity.CoveringNumber
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.CoveringNumber. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_ENNReal_F000
import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F000
import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F001
import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F002
import Definitions.Def_BrownianMotion_Auxiliary_Nat_F000
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

@[expose] public section

open EMetric Set Metric
open scoped ENNReal NNReal

section PseudoEMetricSpace

variable {E : Type*} [PseudoEMetricSpace E] {r ε ε' : ℝ≥0} {A B C : Set E}

lemma TotallyBounded.coveringNumber_ne_top (hA : TotallyBounded A) {r : ℝ≥0} (hr : r ≠ 0) :
    coveringNumber r A ≠ ⊤:= by
  obtain ⟨C, hC_subset, hC_finite, hC_cov⟩ := exists_finite_isCover_of_totallyBounded hr hA
  refine ne_top_of_le_ne_top (b := C.encard) ?_ (IsCover.coveringNumber_le_encard hC_subset hC_cov)
  simpa
end PseudoEMetricSpace

section Volume

open MeasureTheory

section PseudoEMetricSpace
variable {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0} {s N : Set X}

end PseudoEMetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ε : ℝ≥0} {A : Set E} {C : Set E}

end Volume


