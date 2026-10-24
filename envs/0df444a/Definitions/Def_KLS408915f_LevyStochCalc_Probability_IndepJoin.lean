-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
-- name    : KLS408915f_LevyStochCalc_Probability_IndepJoin
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:18:21.28092+00:00
-- url     : https://prove2.me/theorems/c9b3baf5-54c8-4357-86ba-bafa14ffdfcc
-- title:
--   Intersection sets for joins of sigma-algebras
-- statement:
--   Vendored from LevyStochCalc (https://github.com/cgarryZA/LevyStochCalc). `interSets m₁ m₂` is the set of measurable intersections $A	extrm{ intersect }B$ with $A$ measurable for $m_1$ and $B$ measurable for $m_2$. It is the elementary pi-system used by downstream independence-of-joins results; the declarations in this bundle only define this family.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L26-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, definition bundle `KLS408915f_LevyStochCalc_Probability_IndepJoin`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
/-- The π-system of intersections `A ∩ B` with `A ∈ m₁` and `B ∈ m₂`. -/
def interSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ s = A ∩ B}
end Probability
end LevyStochCalc


