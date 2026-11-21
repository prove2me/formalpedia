-- Prove2me | Definitions.Def_SourceProof_829250bf02c9d1529c59983e
-- name    : SourceProof_829250bf02c9d1529c59983e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:33.133665+00:00
-- url     : https://prove2.me/theorems/3e7da953-2c59-47af-93f7-b41a0804de9b
-- title:
--   LevyStochCalc source module: SourceProof_829250bf02c9d1529c59983e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le` comes from the `LevyStochCalc.Brownian.VectorItoProcessWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Window moments of a vector Itô process

Integrating the increment moments of a version of a vector Itô process over a time window gives
bounds on the joint integrals `∫∫_{(u,v]} 𝔼‖X_s − X_u‖ ds` and `∫∫_{(u,v]} 𝔼‖X_s − X_u‖² ds`,
which are what the Riemann-sum estimates consume.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le` — the `L¹` window
  bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le` — the `L²`
  window bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorWindow

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_829250bf02c9d1529c59983e
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u) * ((n : ℝ)
        * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))))) := by
  have hjoint : Measurable (Function.uncurry fun ω s => ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((h.measurable_uncurry.sub ((h.measurable u).comp measurable_fst)).norm).pow_const 2)
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := P) (ν := volume.restrict (Set.Ioc u v))
    (f := fun ω s => ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2)) hjoint.aemeasurable
  rw [hswap]
  have hvu : (0 : ℝ) ≤ v - u := sub_nonneg.mpr huv
  have hbnd : (0 : ℝ) ≤ (n : ℝ)
      * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))) := by positivity
  have hinner : ∀ s ∈ Set.Ioc u v, ∫⁻ ω, ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ)
        * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u))))) := by
    intro s hs
    obtain ⟨hint, hle⟩ := h.integral_sq_norm_sub_le hC0 hCH hbm hB0 hB hu hs.1.le
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
    have hsu : (0 : ℝ) ≤ s - u := sub_nonneg.mpr hs.1.le
    have hsv : s - u ≤ v - u := by linarith [hs.2]
    gcongr
  calc ∫⁻ s in Set.Ioc u v, ∫⁻ ω, ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2) ∂P ∂volume
      ≤ ∫⁻ _s in Set.Ioc u v, ENNReal.ofReal ((n : ℝ)
          * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u))))) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Ioc hinner
    _ = ENNReal.ofReal ((n : ℝ)
          * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))))
          * ENNReal.ofReal (v - u) := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal ((v - u) * ((n : ℝ)
          * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))))) := by
        rw [← ENNReal.ofReal_mul hbnd, mul_comm]
end VectorWindow

end LevyStochCalc.Brownian.Ito


