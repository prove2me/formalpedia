-- Prove2me | Definitions.Def_SourceProof_6f4950440bc6215e53cdb394
-- name    : SourceProof_6f4950440bc6215e53cdb394
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:49:09.789774+00:00
-- url     : https://prove2.me/theorems/bc641607-1bb9-4407-b314-2bd4574a3316
-- title:
--   LevyStochCalc source module: SourceProof_6f4950440bc6215e53cdb394
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002

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


theorem _root_.Prove2MeSourceProof.h_6f4950440bc6215e53cdb394
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  set c : ℝ := 2 * K₁ with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hbnd : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro i ω s
    refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le hc0 ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)|
        ≤ |LevyStochCalc.coordDeriv f' p (Y i s ω)| + |LevyStochCalc.coordDeriv f' p (X s ω)| :=
          LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _
      _ ≤ K₁ + K₁ := add_le_add (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (LevyStochCalc.abs_coordDeriv_le hf'bd p _)
      _ = c := by rw [hc]; ring
  have hjoint : ∀ i : ℕ, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) := by
    intro i
    exact (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp (hYm i)).sub
      ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hXm)).mul hmG
  have hFmeas : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_energyDensity (hjoint i) T
  have hGmeas : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hmG T
  -- inner limit, for almost every path
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun i : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (𝓝 0) := by
    filter_upwards [hae, MeasureTheory.ae_lt_top hGmeas hqG.ne] with ω hω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (i : ℕ) (s : ℝ) =>
        (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun i => (((Measurable.of_uncurry_left (hjoint i)).nnnorm).coe_nnreal_ennreal).pow_const 2)
      (fun i => Filter.Eventually.of_forall fun s => hbnd i ω s) ?_ ?_
    · simpa using hlim
    · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [hω] with s hs
      have hcd : Filter.Tendsto (fun i : ℕ => LevyStochCalc.coordDeriv f' p (Y i s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) :=
        (LevyStochCalc.continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs
      have hconstX : Filter.Tendsto (fun _ : ℕ => LevyStochCalc.coordDeriv f' p (X s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) := tendsto_const_nhds
      have hconstG : Filter.Tendsto (fun _ : ℕ => G ω s) Filter.atTop (𝓝 (G ω s)) :=
        tendsto_const_nhds
      have hzero : Filter.Tendsto (fun i : ℕ =>
          (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) Filter.atTop (𝓝 0) := by
        have hs2 := (hcd.sub hconstX).mul hconstG
        simpa using hs2
      have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        have h1 : Continuous fun x : ℝ => (‖x‖₊ ^ 2 : ℝ≥0) := continuous_nnnorm.pow 2
        have h2 := ENNReal.continuous_coe.comp h1
        simp only [Function.comp_def, ENNReal.coe_pow] at h2
        exact h2
      have hres := (hcont.tendsto (0 : ℝ)).comp hzero
      simp only [Function.comp_def] at hres
      have hz0 : ((‖(0 : ℝ)‖₊ : ℝ≥0∞)) ^ 2 = 0 := by simp
      rw [hz0] at hres
      exact hres
  have hdom : ∀ (i : ℕ) (ω : Ω), (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i ω
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact MeasureTheory.lintegral_mono fun s => hbnd i ω s
  -- outer limit
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (i : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun i => Filter.Eventually.of_forall fun ω => hdom i ω) ?_ hinner
  · simpa using hlim
  · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hqG).ne
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


