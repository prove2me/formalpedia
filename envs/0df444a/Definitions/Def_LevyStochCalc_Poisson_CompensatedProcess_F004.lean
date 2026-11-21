-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F004
-- name    : LevyStochCalc_Poisson_CompensatedProcess_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:34:45.169326+00:00
-- url     : https://prove2.me/theorems/d262ea53-b087-4c14-ab6c-eeeef2314f4c
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001
import Definitions.Def_SourceProof_278d2487462db88d9db97988
import Definitions.Def_SourceProof_35156ff6984aa5b4b399bdef
import Definitions.Def_SourceProof_95e247e701da3178181c6103

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

end Process

section Isometry

include hℱ in
/-- The process is a martingale on the right-continuous natural filtration. -/
theorem martingale_rightCont_process :
    Martingale (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P := by
  refine _root_.Prove2MeSourceProof.h_35156ff6984aa5b4b399bdef
    (_root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) fun s => ?_
  have hF_aesm : ∀ t, AEStronglyMeasurable (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
    P :=
    fun t => (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (_root_.Prove2MeSourceProof.h_95e247e701da3178181c6103 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
    (Eventually.of_forall fun r => bot_le)
    (Eventually.of_forall fun r => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      ((hF_aesm r).sub (hF_aesm s)))
end Isometry

end LevyStochCalc.Poisson.Compensated


