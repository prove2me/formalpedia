-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001
-- name    : LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:44:08.09318+00:00
-- url     : https://prove2.me/theorems/e530b879-eff0-467e-bffe-597475e0363c
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityShiftedAverages
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityShiftedAverages. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000

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

/-- **Predictability of `predictableDyadicSimple_brownian`.** Each `ξ_i`
is `ℱ_{t_i}`-StronglyMeasurable when `g` is progressively measurable. -/
lemma predictableDyadicSimple_brownian_adapted
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (n : ℕ)
    (i : Fin (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.castSucc))
      ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).ξ i) := by
  change @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (dyadicPartition_brownian T n i.castSucc))
    (dyadicAvg_shifted_brownian T g n i)
  exact dyadicAvg_shifted_brownian_adapted ℱ T g h_progMeas n i
/-- **Doubling measure instance for `(volume : Measure ℝ)`.** Mathlib's
`IsUnifLocDoublingMeasure` is not auto-inferred for `ℝ`; we provide it explicitly
via `Real.volume_closedBall` and the trivial doubling constant `K = 2`.

Once available, this unlocks `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`,
which gives the Lebesgue differentiation theorem in the form needed for
sub-lemma A (a.e. convergence of dyadic averages). -/
instance instIsUnifLocDoublingMeasureRealVolume :
    IsUnifLocDoublingMeasure (volume : Measure ℝ) := by
  refine ⟨(2 : NNReal), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε x
  rw [Real.volume_closedBall, Real.volume_closedBall]
  rw [ENNReal.coe_ofNat]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
    rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
    simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


