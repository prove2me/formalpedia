-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionMaster_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:09:08.443672+00:00
-- url     : https://prove2.me/theorems/133c41f3-c5c6-4e1b-a26f-6272ef71a014
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionMaster
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionMaster. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The master integral `simpleIntegral W (masterApprox n) t` lifted to `Lp ℝ 2 P`
(for `0 ≤ t ≤ n+1`; `0` otherwise). The Itô integral process is its `L²`-limit. -/
noncomputable def masterLp (t : ℝ) (n : ℕ) : MeasureTheory.Lp ℝ 2 P :=
  if h : 0 ≤ t ∧ t ≤ (n : ℝ) + 1 then
    (_root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ (master_horizon_pos n)
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) h.1 h.2).toLp
  else 0
include hℱ in
lemma masterLp_coeFn {t : ℝ} (n : ℕ) (ht_nn : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) :
    (masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n : Ω → ℝ)
      =ᵐ[P] fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
        h_sq_int_global n) t ω := by
  rw [masterLp, dif_pos ⟨ht_nn, htn⟩]
  exact MeasureTheory.MemLp.coeFn_toLp _
end MasterSequence

end LevyStochCalc.Brownian.Ito


