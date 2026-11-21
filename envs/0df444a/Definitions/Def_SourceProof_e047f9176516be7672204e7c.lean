-- Prove2me | Definitions.Def_SourceProof_e047f9176516be7672204e7c
-- name    : SourceProof_e047f9176516be7672204e7c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:03:43.680976+00:00
-- url     : https://prove2.me/theorems/68730541-474d-47ee-bfbd-fb87241f1c20
-- title:
--   LevyStochCalc source module: SourceProof_e047f9176516be7672204e7c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le` comes from the `LevyStochCalc.Ito.VectorItoProcessDiff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_SourceProof_700488d66fa58fc241f21293
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8
import Definitions.Def_SourceProof_ea5efb46f0ff2335ed0cf2ed

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `L²` distance between two vector Itô processes

Two vector Itô processes with the same initial value differ by the time integral of the difference
of their drifts and the Itô integral of the difference of their diffusion matrices. Cauchy–Schwarz
bounds the first in `L²` by the energy of the drift difference and the Itô isometry identifies the
second with the energy of the diffusion difference.

The file sits in the `Ito` layer only because the Cauchy–Schwarz bound
`LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le` lives there; nothing here depends on the
Picard construction itself.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le` — the bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Diff

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)


theorem _root_.Prove2MeSourceProof.h_e047f9176516be7672204e7c
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k)))
    (hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k))
    (hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k)))
    (hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k))
    (hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    {t : ℝ} (ht : 0 < t)
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  classical
  have hXm₁ : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t) :=
    LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ hX₀ hbm₁ t
  have hXm₂ : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t) :=
    LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ hX₀ hbm₂ t
  have hcoordm : ∀ p : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 := by
    intro p
    exact ((((measurable_pi_apply p).comp hXm₂).sub
      ((measurable_pi_apply p).comp hXm₁)).nnnorm.coe_nnreal_ennreal).pow_const 2
  -- reduce to the coordinates
  have hred : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [← MeasureTheory.lintegral_finsetSum _ fun p _ => hcoordm p]
    refine MeasureTheory.lintegral_mono fun ω => ?_
    simpa using LevyStochCalc.Brownian.Ito.sq_enorm_pi_le_sum (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω)
  refine hred.trans (Finset.sum_le_sum fun p _ => ?_)
  -- split the coordinate difference into a drift part and a martingale part
  have hsplit : ∀ ω : Ω,
      LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p
      = (((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume))
        + (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω) := by
    intro ω
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    ring
  have hDbm : Measurable fun ω : Ω =>
      (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 :=
    ((((LevyStochCalc.measurable_setIntegral (hbm₂ p) _).sub
      (LevyStochCalc.measurable_setIntegral (hbm₁ p) _)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDmm : Measurable fun ω : Ω =>
      (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((((LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)).nnnorm
        ).coe_nnreal_ennreal).pow_const 2
  have hsum : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 2 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
            - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    have hmono : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (2 * (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
              - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
              - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hsplit ω]
      have := LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul
        ((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume)
        (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω)
      refine this.trans (le_of_eq ?_)
      rw [mul_add]
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.lintegral_add_left (hDbm.const_mul 2),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
  refine hsum.trans (add_le_add ?_ ?_)
  · -- the drift part, by Cauchy–Schwarz
    have hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _)
        (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) t ht
    have heq : ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p t ht),
        LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p t ht)] with ω h1 h2
      rw [MeasureTheory.integral_sub h2 h1]
    rw [heq]
    exact mul_le_mul' le_rfl
      (_root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f
        ((hbm₂ p).sub (hbm₁ p)) ht.le hfin)
  · -- the martingale part, by the difference isometry
    have hM : ∀ ω : Ω, LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω
        = ∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω) := by
      intro ω
      rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale, LevyStochCalc.Brownian.Ito.vectorItoMartingale, ← Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      exact ((((LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t).sub
        (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t)).nnnorm
          ).coe_nnreal_ennreal).pow_const 2
    have hstep : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      rw [← MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k,
        ← MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤)]
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hM ω]
      exact _root_.Prove2MeSourceProof.h_ea5efb46f0ff2335ed0cf2ed _
    refine mul_le_mul' le_rfl (hstep.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => ?_)))
    exact le_of_eq (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 (W.W k) ℱ (hcoord k)
      (H₂ p k) (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) ht)
end Diff

end LevyStochCalc.Brownian.Ito


