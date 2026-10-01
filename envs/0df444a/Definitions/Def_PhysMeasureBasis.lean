-- Prove2me | Definitions.Def_PhysMeasureBasis
-- name    : PhysMeasureBasis
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:15:24.56918+00:00
-- url     : https://prove2.me/theorems/7d56978b-3cbd-49c0-9e64-132dc0db36f3
-- title:
--   Chapter PhysMeasureBasis
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/PhysMeasureBasis.lean`): generated def bundle for PhysMeasureBasis. See BookProof/PhysMeasureBasis.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/PhysMeasureBasis.lean

import Mathlib


/-!
# Part 1: Foundations — measure theory

This file formalizes the measure-theoretic foundations (F1–F8) of the
`pnp.tex` formalization plan.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace PhysMeasureBasis

/-- The unit interval as a measure space: Lebesgue restricted to [0,1]. -/
abbrev unitMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

/-- The unit square with Lebesgue measure. -/
abbrev squareMeasure : Measure (ℝ × ℝ) :=
  volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor ; norm_num

instance : IsProbabilityMeasure squareMeasure := by
  constructor;
  erw [ MeasureTheory.Measure.restrict_apply_univ ] ; ring ;
  erw [ MeasureTheory.Measure.prod_prod ] ; norm_num

/-! ### F1. Points are null in continuous probability spaces -/





/-! ### F2. Countable sets are null -/



/-! ### F3. Selection exists: disintegration / regular conditional probability -/



/-! ### F4. No complete history realizes the selected event -/



/-! ### F5. A finite measure has countably many point atoms -/



/-! ### F6. Continuous and atomic parts are mutually singular -/



/-! ### F7. A jump separates a mixed CDF from a continuous one -/



/-! ### F8. Conditioning a mixed measure on its diffuse part -/



end PhysMeasureBasis


