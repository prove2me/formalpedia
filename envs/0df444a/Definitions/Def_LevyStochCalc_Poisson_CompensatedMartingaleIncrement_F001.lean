-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001
-- name    : LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T17:03:29.553838+00:00
-- url     : https://prove2.me/theorems/ea49a556-10b6-4d53-a7dc-6547c12a76d2
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedMartingaleIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedMartingaleIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Clamped compensator and increment boxes of the compensated simple integral

The compensator `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` of the quadratic variation in its explicit
clamped form `∑_i ν̂(timeRect i t) · ξᵢ²`, the a.e. decomposition of the increment
`simpleIntegral t − simpleIntegral s` over the increment rectangles
`timeRect i t \ timeRect i s` (each a clean box `Ioc a b ×ˢ Aᵢ`), and the box-level moment
identities behind the set-level isometry: independence of a future box increment from the
past, the weighted diagonal second moment, the vanishing of the weighted off-diagonal cross
terms, and cross-integrability of two compensated masses.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/

/-- `Ioc a B \ Ioc a c = Ioc c B` when `a ≤ c`. -/
lemma Ioc_diff_Ioc_left_eq {a c B : ℝ} (hac : a ≤ c) :
    Set.Ioc a B \ Set.Ioc a c = Set.Ioc c B := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ioc, not_and, not_le]
  constructor
  · rintro ⟨⟨hax, hxB⟩, h2⟩
    exact ⟨h2 hax, hxB⟩
  · rintro ⟨hcx, hxB⟩
    exact ⟨⟨lt_of_le_of_lt hac hcx, hxB⟩, fun _ => hcx⟩
/-! ### Set-level quadratic-variation isometry

The increment squares onto the increment boxes; off-diagonal cross terms vanish
(independence + zero mean), and diagonal terms give the box intensities
(independence + `compensated_second_moment`). -/

end LevyStochCalc.Poisson.Compensated


