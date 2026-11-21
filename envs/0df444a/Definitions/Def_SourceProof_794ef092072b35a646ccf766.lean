-- Prove2me | Definitions.Def_SourceProof_794ef092072b35a646ccf766
-- name    : SourceProof_794ef092072b35a646ccf766
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:05.832292+00:00
-- url     : https://prove2.me/theorems/840f29d7-2dd9-4ebb-a371-2b3144076ba9
-- title:
--   LevyStochCalc source module: SourceProof_794ef092072b35a646ccf766
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.contraction_real_core` comes from the `LevyStochCalc.BSDEJ.PicardContractionBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F000
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy and pointwise bounds behind the Picard contraction

The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm, the energy of a difference of two processes is finite when both energies are, and
freezing a process at the horizon leaves its energy there unchanged. At almost every time of the
horizon, twice the pairing of a process against the difference of two evaluations of a Lipschitz
generator is at most `β / 2` times the second moment of the process plus `6 L² / β` times the
sample energy density of the differenced arguments, and the real-variable core turns a weighted
energy dominated by such a pairing into a contraction by the factor `6 L² / β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

end Pointwise

section RealCore


theorem _root_.Prove2MeSourceProof.h_794ef092072b35a646ccf766 {A Gout Gin V : ℝ → ℝ} {β c T : ℝ} (hβ : 2 ≤ β)
    (hA0 : ∀ s, 0 ≤ A s)
    (hAint : IntegrableOn (fun s => Real.exp (β * s) * A s) (Set.Icc (0 : ℝ) T))
    (hGoutint : IntegrableOn (fun s => Real.exp (β * s) * Gout s) (Set.Icc (0 : ℝ) T))
    (hGinint : IntegrableOn (fun s => Real.exp (β * s) * Gin s) (Set.Icc (0 : ℝ) T))
    (hVint : IntegrableOn (fun s => Real.exp (β * s) * V s) (Set.Icc (0 : ℝ) T))
    (hL : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s)
    (hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), V s ≤ β / 2 * A s + c * Gin s) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s
      ≤ c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
  have hM0 : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s :=
    setIntegral_nonneg measurableSet_Icc fun s _ => mul_nonneg (Real.exp_nonneg _) (hA0 s)
  have h1 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      = (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s)
        + (β - 1) * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s := by
    have hc1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (Gout s + (β - 1) * A s)
          = Real.exp (β * s) * Gout s + (β - 1) * (Real.exp (β * s) * A s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc1, integral_add hGoutint (hAint.const_mul (β - 1)),
      integral_const_mul]
  have hRHSint : IntegrableOn
      (fun s => Real.exp (β * s) * (β / 2 * A s + c * Gin s)) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.congr ((hAint.const_mul (β / 2)).add (hGinint.const_mul c)) ?_
    filter_upwards with s
    simp only [Pi.add_apply]
    ring
  have h2 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s) := by
    refine integral_mono_ae hVint hRHSint ?_
    filter_upwards [hpt] with s hs
    exact mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have h3 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s)
      = β / 2 * (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s)
        + c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
    have hc3 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (β / 2 * A s + c * Gin s)
          = β / 2 * (Real.exp (β * s) * A s) + c * (Real.exp (β * s) * Gin s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc3, integral_add (hAint.const_mul (β / 2)) (hGinint.const_mul c),
      integral_const_mul, integral_const_mul]
  rw [h1] at hL
  have hfin := hL.trans (h2.trans_eq h3)
  nlinarith [hfin, mul_nonneg (by linarith : (0 : ℝ) ≤ β - 2) hM0]
end RealCore

end LevyStochCalc.BSDEJ.Solves


