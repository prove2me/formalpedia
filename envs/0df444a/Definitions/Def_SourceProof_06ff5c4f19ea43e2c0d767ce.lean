-- Prove2me | Definitions.Def_SourceProof_06ff5c4f19ea43e2c0d767ce
-- name    : SourceProof_06ff5c4f19ea43e2c0d767ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:35:48.394327+00:00
-- url     : https://prove2.me/theorems/fe0f6b0f-e84f-4bfb-b1da-7e2ff11960d5
-- title:
--   LevyStochCalc source module: SourceProof_06ff5c4f19ea43e2c0d767ce
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` comes from the `LevyStochCalc.Brownian.ItoQuadVarRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000
import Definitions.Def_SourceProof_44f5bfd0fb515ee218ff3537

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation Riemann sum of the Itô formula

Squaring the increments of a continuous Itô process across a uniform grid and weighting them by
a bounded Lipschitz function of the process gives a Riemann sum for `∫_0^T φ(X_s)·H_s² ds`. The
drift square and the cross term are `O(1/m)` and `O(m^{-1/2})`, the compensated squares are
`O(m^{-1/2})` by the martingale-difference bound, and the compensator itself is a frozen-weight
Riemann sum for the density `H²`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le` — the drift-square sum.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` — the cross term.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` — the compensated
  squares.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` — the four
  pieces together.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarRiemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_06ff5c4f19ea43e2c0d767ce
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (2 * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω))| ∂P
        ≤ (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ)))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hMdata : ∀ i : ℕ,
      MeasureTheory.Integrable (fun ω : Ω =>
          |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω|) P
        ∧ ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ∂P
          ≤ C * Real.sqrt (T / (m : ℝ)) := by
    intro i
    obtain ⟨hint, hle⟩ := _root_.Prove2MeSourceProof.h_44f5bfd0fb515ee218ff3537 W ℱ hℱ H hm hp hq hC0 hCH
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
    rw [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at hle
    exact ⟨hint, hle⟩
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
    rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at hle
  have hmeas : Measurable fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
      * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) :=
    Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
        ((measurable_const.mul (LevyStochCalc.measurable_setIntegral_Ioc hbm _ _)).mul
          (LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))))
  set g : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ)))
    * |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| with hgdef
  have hgint : MeasureTheory.Integrable g P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => ((hMdata i).1.const_mul _)
  have hbound : ∀ ω : Ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
      * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))| ≤ g ω := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)|
          * (2 * |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              bdrift ω s ∂volume|
            * |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω|)
        ≤ Kφ * (2 * (B * (T / (m : ℝ)))
            * |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω|) := by
          gcongr
          · exact hφbd _
          · exact hDbd ω i
      _ = 2 * Kφ * (B * (T / (m : ℝ)))
            * |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| := by ring
  have hLint : MeasureTheory.Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))) P := by
    refine hgint.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hbound ω).trans (le_abs_self _)
  refine ⟨hLint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))| ∂P
      ≤ ∫ ω, g ω ∂P := MeasureTheory.integral_mono hLint.abs hgint hbound
    _ = ∑ i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ)))
          * ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ∂P := by
        rw [hgdef, MeasureTheory.integral_finsetSum _ fun i _ => ((hMdata i).1.const_mul _)]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range m, 2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hc : (0 : ℝ) ≤ 2 * Kφ * (B * (T / (m : ℝ))) := by positivity
        exact mul_le_mul_of_nonneg_left (hMdata i).2 hc
    _ = (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end QuadVarRiemann

end LevyStochCalc.Brownian.Ito


