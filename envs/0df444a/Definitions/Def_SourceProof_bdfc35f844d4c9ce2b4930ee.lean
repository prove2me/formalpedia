-- Prove2me | Definitions.Def_SourceProof_bdfc35f844d4c9ce2b4930ee
-- name    : SourceProof_bdfc35f844d4c9ce2b4930ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:26:48.120722+00:00
-- url     : https://prove2.me/theorems/4df6cb8f-1bc2-4c01-8a97-d03c81224988
-- title:
--   LevyStochCalc source module: SourceProof_bdfc35f844d4c9ce2b4930ee
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_186e21643bf26d9e554362b3
import Definitions.Def_SourceProof_560d23a90584c8e4562d928f
import Definitions.Def_SourceProof_6be12e51c788a72f4de041a3
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to the right-continuation `ℱ₊` of
`ℱ`, and the compensator `∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property
of the compensated square.
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

include h_meas h_progMeas h_sq_int_global in

theorem _root_.Prove2MeSourceProof.h_bdfc35f844d4c9ce2b4930ee {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
          ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P)
      Filter.atTop (nhds 0) := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hν
    set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
    set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
    have hHp_meas : Measurable Hp := h_meas
    have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
    have hHmem := _root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H h_meas h_sq_int_global ht'
    -- `Gp n → Hp` in `L²(P ⊗ ν)`.
    have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      intro f hf
      rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
          MeasureTheory.lintegral_prod _
            (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
    have hfin2 : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
        MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ :=
      fun f hf hfv => lt_top_iff_ne_top.mpr (fun h => hfv (by
        rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]))
    have hL2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
      have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                ∂volume ∂P := by
        intro n
        rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
        refine lintegral_congr (fun ω =>
          MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
        simp only [Pi.sub_apply, hGp, hHp]
        rw [show (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω - H ω s
              = -(H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω)
            from by ring, nnnorm_neg]
      have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
          Filter.atTop (nhds 0) := by
        simp_rw [hsq]
        exact _root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := t) ℱ H h_meas h_progMeas h_sq_int_global
      have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      refine h3.congr (fun n => ?_)
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
    -- squares converge in `L¹(P ⊗ ν)`.
    have hjoint : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν))
        Filter.atTop (nhds 0) :=
      _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3 (fun n => (hGp_meas n).aemeasurable) hHp_meas.aemeasurable
        hHmem.2.ne hL2
    -- marginal `L¹(P)` ≤ joint `L¹(P ⊗ ν)`.
    have hmarg : ∀ n, MeasureTheory.eLpNorm
        (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
        ≤ MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν) := by
      intro n
      set dsq : Ω × ℝ → ℝ := fun p => (Gp n p) ^ 2 - (Hp p) ^ 2 with hdsq
      have hGsq_int : MeasureTheory.Integrable (fun p => (Gp n p) ^ 2) (P.prod ν) :=
        MeasureTheory.MemLp.integrable_sq
          (show MeasureTheory.MemLp (Gp n) 2 (P.prod ν) from
            ⟨(hGp_meas n).aestronglyMeasurable, hfin2 (Gp n) (hGp_meas n)
              (_root_.Prove2MeSourceProof.h_186e21643bf26d9e554362b3
                (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t).ne⟩)
      have hHsq_int : MeasureTheory.Integrable (fun p => (Hp p) ^ 2) (P.prod ν) :=
        hHmem.integrable_sq
      have hdsq_int : MeasureTheory.Integrable dsq (P.prod ν) := hGsq_int.sub hHsq_int
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        MeasureTheory.lintegral_prod _ hdsq_int.aestronglyMeasurable.enorm]
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hGsq_int.prod_right_ae, hHsq_int.prod_right_ae] with ω hGω hHω
      have hcomb : (∫ u in Set.Icc (0 : ℝ) t,
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume
          = ∫ u, dsq (ω, u) ∂ν := by
        rw [hdsq]; exact (MeasureTheory.integral_sub hGω hHω).symm
      rw [hcomb]
      exact MeasureTheory.enorm_integral_le_lintegral_enorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjoint
      (Filter.Eventually.of_forall (fun n => bot_le)) (Filter.Eventually.of_forall hmarg)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    symm
    rw [← ht']
    have hz : (fun ω => (∫ u in Set.Icc (0 : ℝ) (0 : ℝ),
        ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) := by
      funext ω
      rw [Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp),
        MeasureTheory.setIntegral_measure_zero _ (by simp), sub_zero]; rfl
    rw [hz, MeasureTheory.eLpNorm_zero]
end MasterSequence

end LevyStochCalc.Brownian.Ito


