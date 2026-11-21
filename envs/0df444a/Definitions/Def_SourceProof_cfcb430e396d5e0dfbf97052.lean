-- Prove2me | Definitions.Def_SourceProof_cfcb430e396d5e0dfbf97052
-- name    : SourceProof_cfcb430e396d5e0dfbf97052
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:53:28.222867+00:00
-- url     : https://prove2.me/theorems/5b912ff5-01ce-451f-8818-07686b455195
-- title:
--   LevyStochCalc source module: SourceProof_cfcb430e396d5e0dfbf97052
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_diffusionIntegrand_clamp` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_SourceProof_29f970bc85115e70732226f2
import Definitions.Def_SourceProof_6f4950440bc6215e53cdb394

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of the clamped approximation of a vector Itô process

For a function whose first and second derivatives are bounded, the drift integrals, the quadratic
variation terms and the diffusion integrands built from the coefficients clamped at a level growing
to infinity converge to the ones built from the original coefficients: the drift and quadratic
variation terms pathwise, the diffusion integrands in energy on a bounded window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)


theorem _root_.Prove2MeSourceProof.h_cfcb430e396d5e0dfbf97052
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
          - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by
  have hnsTop : Filter.Tendsto ns Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hge Filter.tendsto_id
  have hclamp : Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) :=
    (_root_.Prove2MeSourceProof.h_29f970bc85115e70732226f2 (hm p k) (hq p k).ne).comp hnsTop
  have hderiv := _root_.Prove2MeSourceProof.h_6f4950440bc6215e53cdb394 hf'c hK₁0 hf'bd (hm p k) (hq p k)
    hYm hXm hae p
  have hbound : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
        - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
          * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
        + 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      := by
    intro i ω s
    have hsplit : LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
        - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s
        = LevyStochCalc.coordDeriv f' p (Y i s ω) * (LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s)
          + (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s := by ring
    rw [hsplit]
    set A : ℝ := LevyStochCalc.coordDeriv f' p (Y i s ω) * (LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s) with hA
    set B : ℝ := (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s with hB
    have hAle : (‖A‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (K₁ ^ 2)
          * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 := by
      rw [hA]
      refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le hK₁0 ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (abs_nonneg _)
    calc (‖A + B‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖A‖₊ : ℝ≥0∞) ^ 2 + (‖B‖₊ : ℝ≥0∞) ^ 2) := LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul A B
      _ = 2 * (‖A‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by rw [mul_add]
      _ ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
            * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
          + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by
          exact add_le_add (mul_le_mul' le_rfl hAle) le_rfl
  have hlimbound : Filter.Tendsto (fun i : ℕ =>
      2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun i : ℕ =>
        2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal (K₁ ^ 2)) hclamp
        (Or.inr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
      rw [mul_zero] at hc
      exact hc.congr fun i => by rw [mul_assoc]
    have h2 : Filter.Tendsto (fun i : ℕ =>
        2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hderiv (Or.inr (by simp))
      rw [mul_zero] at hc
      exact hc
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimbound
    (fun i => zero_le) (fun i => ?_)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
          - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (2 * (ENNReal.ofReal (K₁ ^ 2)
              * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            + 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω =>
          MeasureTheory.lintegral_mono fun s => hbound i ω s
    _ = _ := by
        have hAm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
            ENNReal.ofReal (K₁ ^ 2)
              * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2) :=
          ((((LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm (ns i) p k).sub
            (hm p k)).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.const_mul _
        rw [LevyStochCalc.Brownian.Ito.lintegral_window_add
            (g := fun ω s => 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (hAm.const_mul _) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => ENNReal.ofReal (K₁ ^ 2)
                * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp : ENNReal.ofReal (K₁ ^ 2) ≠ ⊤) T]
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


