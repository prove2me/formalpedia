-- Prove2me | Definitions.Def_SourceProof_354da4a27d9d8ca282c89b8e
-- name    : SourceProof_354da4a27d9d8ca282c89b8e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:46:18.121261+00:00
-- url     : https://prove2.me/theorems/49624616-ac74-4836-81f2-38847cddbb7c
-- title:
--   LevyStochCalc source module: SourceProof_354da4a27d9d8ca282c89b8e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` comes from the `LevyStochCalc.Brownian.ItoFormulaScalar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_47110770aca16d7a3084f758

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a scalar Itô process

For a continuous adapted version `X` of `X₀ + ∫ b ds + ∫ H dW` with bounded coefficients and
`f` twice differentiable with bounded derivatives and a Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. The proof telescopes the second-order Taylor expansion over a uniform grid and
bounds the four resulting errors, all of which vanish as the mesh does.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoGridError` — the `L¹` error of the grid approximation, as a
  function of the mesh.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` — that error bounds the
  `L¹` defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` — Itô's formula.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_354da4a27d9d8ca282c89b8e
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hX₀ : Measurable X₀) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {K₁ K₂ : ℝ} (hf'bd : ∀ x, |f' x| ≤ K₁) (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ x, |f'' x| ≤ K₂)
    {K : ℝ} (hK0 : 0 ≤ K) (hf''lip : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    (hmg : Measurable (Function.uncurry fun ω s => f' (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => f' (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖f' (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume := by
  have hgrid : ∀ m : ℕ, m ≠ 0 →
      MeasureTheory.Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
          - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
            + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω
            + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)) P
        ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
            - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
              + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                  hmg hpg hqg T ω
              + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
          ≤ LevyStochCalc.Brownian.Ito.itoGridError B C T K K₂ (T / (m : ℝ)) := fun m hm0 =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_47110770aca16d7a3084f758 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hX₀ hbm hB0 hB hf hf' hf'bd hK₂0 hf''bd hK0
      hf''lip hmg hpg hqg hT hm0
  obtain ⟨hZint, -⟩ := hgrid 1 one_ne_zero
  have hzero : ∫ ω, |f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P ≤ 0 := by
    refine ge_of_tendsto (LevyStochCalc.Brownian.Ito.tendsto_itoGridError B C T K K₂) ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with m hmpos
    exact (hgrid m hmpos.ne').2
  have hnn : (0 : ℝ) ≤ ∫ ω, |f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P :=
    MeasureTheory.integral_nonneg fun ω => abs_nonneg _
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun ω => abs_nonneg _) hZint.abs).mp (le_antisymm hzero hnn)
  filter_upwards [hae] with ω hω
  have hz : f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume) = 0 :=
    abs_eq_zero.mp hω
  linarith
end Formula

end LevyStochCalc.Brownian.Ito


