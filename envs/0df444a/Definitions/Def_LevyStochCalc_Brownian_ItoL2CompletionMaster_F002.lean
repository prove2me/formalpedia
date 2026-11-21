-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
-- name    : LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:13:11.772176+00:00
-- url     : https://prove2.me/theorems/f0bfeac3-3dd9-48ee-a809-bb4da721c8ce
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionMaster
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionMaster. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F001
import Definitions.Def_SourceProof_7edd2e3de7413bb1cc6dc69c

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

/-- The **L² Itô integral process** as an `Lp ℝ 2 P`-valued function of time: the
`L²`-limit of the master integral sequence. -/
noncomputable def stochasticIntegralBrownianLp (t : ℝ) : MeasureTheory.Lp ℝ 2 P :=
  Filter.limUnder Filter.atTop (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
include hℱ in
/-- Each master integral lies in `lpMeas` — it is `ℱ_t`-measurable. -/
lemma masterLp_mem_lpMeas (t : ℝ) (n : ℕ) :
    masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n
      ∈ MeasureTheory.lpMeas ℝ ℝ
        (ℱ t) 2 P := by
  rw [masterLp]
  split_ifs with h
  · rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    refine ((simpleIntegral_stronglyAdapted_brownian W ℱ hℱ
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)
        t).aestronglyMeasurable).congr ?_
    exact (MeasureTheory.MemLp.coeFn_toLp _).symm
  · exact Submodule.zero_mem _
include hℱ in
/-- The Itô integral process lies in `lpMeas` at each time (closedness of `lpMeas`
+ the `L²`-Cauchy limit of `ℱ_t`-measurable master integrals). -/
lemma stochasticIntegralBrownianLp_mem_lpMeas (t : ℝ) :
    stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t
      ∈ MeasureTheory.lpMeas ℝ ℝ
        (ℱ t) 2 P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hcs : CauchySeq (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) := by
    rcases le_or_gt 0 t with ht | ht
    · exact _root_.Prove2MeSourceProof.h_7edd2e3de7413bb1cc6dc69c W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht
    · have heq : (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
          = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
        funext n; rw [masterLp, dif_neg (fun h => absurd h.1 (not_le.mpr ht))]
      rw [heq]; exact (tendsto_const_nhds (x := (0 : MeasureTheory.Lp ℝ 2 P))).cauchySeq
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
  have hclosed : IsClosed {f : MeasureTheory.Lp ℝ 2 P |
      AEStronglyMeasurable[ℱ t]
        (↑↑f : Ω → ℝ) P} :=
    MeasureTheory.isClosed_aestronglyMeasurable
      (ℱ.le t)
  exact hclosed.mem_of_tendsto hcs.tendsto_limUnder
    (Filter.Eventually.of_forall
      (fun n => MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
        (masterLp_mem_lpMeas W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)))
include hℱ in
/-- `↑↑(Flp t)` is `ℱ_t`-a.e.-strongly-measurable. -/
lemma stochasticIntegralBrownian_aesm (t : ℝ) :
    AEStronglyMeasurable[ℱ t]
      (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) P :=
  MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
    (stochasticIntegralBrownianLp_mem_lpMeas W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
/-- The **L² Itô integral** `t ↦ ∫_0^t H_s dW_s` as a process `ℝ → Ω → ℝ`, taken as
the honest `ℱ_t`-measurable representative of the `L²`-limit. -/
noncomputable def stochasticIntegralBrownian (t : ℝ) : Ω → ℝ :=
  (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).mk
    (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t))
include hℱ in
/-- The integral process is a.e.-equal to the `L²`-limit's `coeFn`. -/
lemma stochasticIntegralBrownian_ae_eq (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global t) : Ω → ℝ) :=
  (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).ae_eq_mk.symm
include hℱ in
/-- The integral process is strongly adapted to the natural filtration. -/
lemma stochasticIntegralBrownian_stronglyAdapted :
    MeasureTheory.StronglyAdapted ℱ
      (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global) :=
  fun t => (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas
    h_sq_int_global t).stronglyMeasurable_mk
end MasterSequence

end LevyStochCalc.Brownian.Ito


