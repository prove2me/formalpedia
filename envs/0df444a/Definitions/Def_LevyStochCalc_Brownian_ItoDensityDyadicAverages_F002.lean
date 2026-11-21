-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002
-- name    : LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:26:17.610245+00:00
-- url     : https://prove2.me/theorems/d88a7d3a-f134-4305-8f54-a1cedb08e2f8
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityDyadicAverages
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityDyadicAverages. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F001
import Definitions.Def_SourceProof_59dc14df6f6315a597b2c358

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).

/-- **Dyadic SimplePredictable (Brownian):** the SimplePredictable obtained by
dyadic refinement of `g` at level `n`. Partition `t_i = i T / 2^n`; coefficient
`ξ_i ω = (2^n/T) · ∫_{t_i}^{t_{i+1}} g(ω, s) ds`.

This SimplePredictable converges to `g` in L²(P × volume) as `n → ∞`. The
convergence is the substantive sub-result (Lévy upward / L² martingale convergence
on the dyadic σ-algebra). -/
noncomputable def dyadicSimplePredictable_brownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartition_brownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvg_brownian (T := T) g n
  ξ_bounded := fun i =>
    ⟨M, fun ω => _root_.Prove2MeSourceProof.h_59dc14df6f6315a597b2c358 T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_brownian_measurable T g h_meas n
end LevyStochCalc.Brownian.Ito


