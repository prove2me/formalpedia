-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001
-- name    : LevyStochCalc_Poisson_CompensatedProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:10:27.992068+00:00
-- url     : https://prove2.me/theorems/d1b13218-1f6f-4951-8b4e-ccd21260fa97
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F000
import Definitions.Def_SourceProof_844e49f4d35b853b668498c9

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

/-- The `L²` integral process at time `t`, as an element of `L²(P)`: the limit of the stage
integrals. -/
noncomputable def processLp (t : ℝ) : Lp ℝ 2 P :=
  limUnder atTop (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n)
include hℱ in
lemma stageLp_tendsto (t : ℝ) :
    Tendsto (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n) atTop
      (𝓝 (processLp N ℱ φ h_meas h_progMeas h_sq_int_global t)) :=
  (_root_.Prove2MeSourceProof.h_844e49f4d35b853b668498c9 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).tendsto_limUnder
include hℱ in
lemma stageLp_mem_lpMeas (t : ℝ) (n : ℕ) :
    stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n
      ∈ lpMeas ℝ ℝ (ℱ t) 2 P := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  refine (((martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).stronglyAdapted
    t).aestronglyMeasurable).congr ?_
  exact (MemLp.coeFn_toLp _).symm
include hℱ in
lemma processLp_mem_lpMeas (t : ℝ) :
    processLp N ℱ φ h_meas h_progMeas h_sq_int_global t
      ∈ lpMeas ℝ ℝ (ℱ t) 2 P := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hclosed : IsClosed {f : Lp ℝ 2 P |
      AEStronglyMeasurable[ℱ t] (↑↑f : Ω → ℝ) P} :=
    isClosed_aestronglyMeasurable (ℱ.le t)
  exact hclosed.mem_of_tendsto (stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
    (Eventually.of_forall fun n => mem_lpMeas_iff_aestronglyMeasurable.mp
      (stageLp_mem_lpMeas N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t n))
include hℱ in
lemma process_aesm (t : ℝ) :
    AEStronglyMeasurable[ℱ t]
      (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) P :=
  mem_lpMeas_iff_aestronglyMeasurable.mp
    (processLp_mem_lpMeas N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
/-- The compensated-Poisson `L²` integral process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`, taken as
the `ℱ_t`-measurable representative of the `L²`-limit of the stage integrals. -/
noncomputable def process (t : ℝ) : Ω → ℝ :=
  (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).mk
    (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t))
include hℱ in
lemma process_ae_eq (t : ℝ) :
    process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) :=
  (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).ae_eq_mk.symm
include hℱ in
lemma process_stronglyAdapted :
    StronglyAdapted ℱ (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) :=
  fun t => (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).stronglyMeasurable_mk
include hℱ in
lemma process_memLp (t : ℝ) : MemLp (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) 2 P :=
  MemLp.ae_eq (process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).symm (Lp.memLp _)
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


