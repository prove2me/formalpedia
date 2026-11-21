-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F004
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineCommon_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:54:35.07595+00:00
-- url     : https://prove2.me/theorems/1e7fb6bd-b408-4d51-93d2-5e626eea65cf
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineCommon
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineCommon. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F002
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F003
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F004
import Definitions.Def_SourceProof_02639dd90be44822908c47b8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Common refinement of two simple predictables and the difference isometry

The common refinement of two `SimplePredictable Ω T` sharing an endpoint: the
merged set of partition points, the merged partition `SimplePredictable.mergedπ`
with its two refining index maps, the induced refinements
`SimplePredictable.commonRefinement_left`/`_right` and their difference
`SimplePredictable.sub_on_common`. These give the difference isometry for simple
integrals (`SimplePredictable.diff_isometry_simple`) and the Cauchy property of
the simple integrals of an `L²`-Cauchy sequence of simple predictables
(`cauchy_of_L2_dense_simple`).
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0b.9: Cauchy preservation for `simpleIntegral`.** If an
eval-sequence of adapted simple integrands sharing a common endpoint is
`L²(λ⊗P)`-Cauchy (in ε-`N` form on the squared `lintegral`), then the
sequence of `simpleIntegral`s is `L²(P)`-Cauchy.

Direct corollary of `diff_isometry_simple` applied pairwise: each
pairwise distance on the integral side equals the corresponding pairwise
distance on the eval side, so the eval-Cauchy ε-`N` witness `N` works
verbatim for the integrals. -/
theorem cauchy_of_L2_dense_simple
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, (‖simpleIntegral W (G n) T ω - simpleIntegral W (G m) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy_eval ε hε
  refine ⟨N, fun n m hn hm => ?_⟩
  rw [_root_.Prove2MeSourceProof.h_02639dd90be44822908c47b8 W ℱ hℱ hT (G n) (G m)
        (h_eq n m) (h_adapt n) (h_adapt m)]
  exact hN n m hn hm
end LevyStochCalc.Brownian.Ito


