-- Prove2me | Definitions.Def_SourceProof_d82a80578e51eb43ce3e150e
-- name    : SourceProof_d82a80578e51eb43ce3e150e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:28:32.86154+00:00
-- url     : https://prove2.me/theorems/63e8ccc6-d4e7-4fa2-9258-56ccc60ba36f
-- title:
--   LevyStochCalc source module: SourceProof_d82a80578e51eb43ce3e150e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` comes from the `LevyStochCalc.Brownian.ItoFormulaGrid` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
import Definitions.Def_SourceProof_5e84cb76e3723bb35ee92ba4
import Definitions.Def_SourceProof_e350717f59f1a5a72381b69b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum

section RiemannLimit

end RiemannLimit

section ItoIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_d82a80578e51eb43ce3e150e
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)| ^ 3 ∂P
      ≤ 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hstep : ∀ i : ℕ, LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) - LevyStochCalc.Brownian.Ito.unifGrid T m i = T / (m : ℝ) :=
    LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := le_of_lt (div_pos hT hm')
  have hK0 : (0 : ℝ) ≤ (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2 := by
    have h1 : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]) (by positivity)
    linarith [sq_nonneg C]
  have hterm : ∀ i ∈ Finset.range m, ∫ ω,
      |(∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)| ^ 3 ∂P
      ≤ 4 * ((B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))) := by
    intro i _
    have hle : LevyStochCalc.Brownian.Ito.unifGrid T m i ≤ LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) := (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
    -- the drift increment
    have hDbd : ∀ ω : Ω,
        |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume|
          ≤ B * (T / (m : ℝ)) := by
      intro ω
      have h := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω) hle
      rwa [hstep i] at h
    have hDint := LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_three (P := P) bdrift hbm hB0 hB hle
    have hDle : ∫ ω, |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        bdrift ω s ∂volume| ^ 3 ∂P ≤ (B * (T / (m : ℝ))) ^ 3 := by
      calc ∫ ω, |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            bdrift ω s ∂volume| ^ 3 ∂P
          ≤ ∫ _ω : Ω, (B * (T / (m : ℝ))) ^ 3 ∂P :=
            MeasureTheory.integral_mono hDint (MeasureTheory.integrable_const _)
              (fun ω => pow_le_pow_left₀ (abs_nonneg _) (hDbd ω) 3)
        _ = (B * (T / (m : ℝ))) ^ 3 := by simp
    -- the martingale increment
    obtain ⟨hMint, hMle⟩ := _root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf W ℱ hℱ H hm hp hq hC0 hCH
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
    rw [hstep i] at hMle
    -- the sum
    have hsumint := _root_.Prove2MeSourceProof.h_e350717f59f1a5a72381b69b W ℱ hℱ H hm hp hq hC0 hCH
      bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
    refine (_root_.Prove2MeSourceProof.h_5e84cb76e3723bb35ee92ba4 hDint hMint hsumint).trans ?_
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    exact mul_le_mul_of_nonneg_left (add_le_add hDle hMle) h4
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  calc (m : ℝ) * (4 * ((B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))))
      = 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ)))) := by ring
    _ = 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := by rw [hTm]
    _ ≤ 4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))) := le_rfl
end ItoIncrement

end LevyStochCalc.Brownian.Ito


