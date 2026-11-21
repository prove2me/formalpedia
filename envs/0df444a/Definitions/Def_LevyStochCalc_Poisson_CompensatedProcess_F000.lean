-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F000
-- name    : LevyStochCalc_Poisson_CompensatedProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:51:02.265971+00:00
-- url     : https://prove2.me/theorems/b47ab41a-c0b7-4f39-a8ba-4a4a25075b0a
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F001

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

/-- The stage-`n` integral at time `t`, as an element of `L²(P)`. -/
noncomputable def stageLp (t : ℝ) (n : ℕ) : Lp ℝ 2 P :=
  (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t).toLp _
lemma stageLp_coeFn (t : ℝ) (n : ℕ) :
    (stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n : Ω → ℝ)
      =ᵐ[P] fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω :=
  MemLp.coeFn_toLp _
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


