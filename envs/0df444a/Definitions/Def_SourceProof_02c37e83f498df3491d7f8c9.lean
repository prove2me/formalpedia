-- Prove2me | Definitions.Def_SourceProof_02c37e83f498df3491d7f8c9
-- name    : SourceProof_02c37e83f498df3491d7f8c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:07:52.631189+00:00
-- url     : https://prove2.me/theorems/30f4cb0b-ac8e-424a-8ef9-369287fc7829
-- title:
--   LevyStochCalc source module: SourceProof_02c37e83f498df3491d7f8c9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.bounded_locallyIntegrable` comes from the `LevyStochCalc.Brownian.ItoDensityShiftedAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.


theorem _root_.Prove2MeSourceProof.h_02c37e83f498df3491d7f8c9
    (g : ℝ → ℝ) (h_meas : Measurable g) (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) :
    MeasureTheory.LocallyIntegrable g volume := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm
    (C := ENNReal.ofReal M) ?_ ?_ ?_
  · simp
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [show ‖g s‖ₑ = ENNReal.ofReal ‖g s‖ from (ofReal_norm _).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs]
    exact h_bound s
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


