-- Prove2me | Definitions.Def_SourceProof_3f24f0fb576e2ea9f8ba092b
-- name    : SourceProof_3f24f0fb576e2ea9f8ba092b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:41:56.362857+00:00
-- url     : https://prove2.me/theorems/446a15f6-1cf9-40e4-baad-b551ed4f1933
-- title:
--   LevyStochCalc source module: SourceProof_3f24f0fb576e2ea9f8ba092b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` comes from the `LevyStochCalc.Brownian.ItoQuadVarRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F001
import Definitions.Def_SourceProof_06ff5c4f19ea43e2c0d767ce
import Definitions.Def_SourceProof_1ba7518b55416238bb307ceb
import Definitions.Def_SourceProof_68d2be4bfe56156e1f930f2e
import Definitions.Def_SourceProof_724ac40b8d5293986a0749a0

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

theorem _root_.Prove2MeSourceProof.h_3f24f0fb576e2ea9f8ba092b
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => (∑ i ∈ Finset.range m,
          φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
        + Real.sqrt (Kφ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2))
        + L * C ^ 2 * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ)))) := by
  have hHsqbd : ∀ (ω : Ω) (s : ℝ), |H ω s ^ 2| ≤ C ^ 2 := by
    intro ω s
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCH ω s) 2
  obtain ⟨hAint, hAle⟩ :=
    h.integral_abs_sum_drift_sq_le hbm hB0 hB hφc hKφ0 hφbd hT hm0
  obtain ⟨hBint, hBle⟩ :=
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_06ff5c4f19ea43e2c0d767ce p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB hφc hKφ0 hφbd hT hm0
  obtain ⟨hCint, hCle⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_1ba7518b55416238bb307ceb p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hφc hKφ0 hφbd hT hm0
  obtain ⟨hDint, hDle⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_68d2be4bfe56156e1f930f2e p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
    (fun ω s => H ω s ^ 2) (hm.pow_const 2) (by positivity) hHsqbd hφc hφbd hL0 hφlip hT hm0
  have hae : ∀ᵐ ω ∂P, ∀ i : ℕ,
      (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2
        = (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2
          + 2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
              * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          + LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          + ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              H ω s ^ 2 ∂volume :=
    MeasureTheory.ae_all_iff.mpr fun i => h.sq_sub_ae hCH hbm hB
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
  have hsplit : (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume)
      =ᵐ[P] fun ω => (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2)
          + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)))
          + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
                (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                  H ω s ^ 2 ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume) := by
    filter_upwards [hae] with ω hω
    have hterm : ∀ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2
        = φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2
          + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
                (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                H ω s ^ 2 ∂volume := by
      intro i _
      rw [hω i]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    ring
  have hsplitabs : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume|)
      =ᵐ[P] fun ω => |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume) ^ 2)
          + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (2 * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift ω s ∂volume)
              * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)))
          + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
                (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                  H ω s ^ 2 ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume)| := by
    filter_upwards [hsplit] with ω hω
    rw [hω]
  refine ⟨(((hAint.add hBint).add hCint).add hDint).congr hsplit.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hsplitabs]
  exact _root_.Prove2MeSourceProof.h_724ac40b8d5293986a0749a0 hAint hBint hCint hDint hAle hBle hCle hDle
end QuadVarRiemann

end LevyStochCalc.Brownian.Ito


