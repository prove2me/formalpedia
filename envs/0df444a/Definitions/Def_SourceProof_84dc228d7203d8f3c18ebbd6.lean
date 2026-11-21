-- Prove2me | Definitions.Def_SourceProof_84dc228d7203d8f3c18ebbd6
-- name    : SourceProof_84dc228d7203d8f3c18ebbd6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:15.443975+00:00
-- url     : https://prove2.me/theorems/5ce9f145-b73a-401a-a27f-320e33f52051
-- title:
--   LevyStochCalc source module: SourceProof_84dc228d7203d8f3c18ebbd6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le` comes from the `LevyStochCalc.Brownian.ItoFormulaScalar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoMartingaleRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F001
import Definitions.Def_SourceProof_33cc866be12cedca71971a8f

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


theorem _root_.Prove2MeSourceProof.h_84dc228d7203d8f3c18ebbd6 {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.AEStronglyMeasurable g P) {V : ℝ} (hV0 : 0 ≤ V)
    (hle : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal V) :
    MeasureTheory.Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ Real.sqrt V := by
  have hmem : MeasureTheory.MemLp g 2 P :=
    LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hg (lt_of_le_of_lt hle (by simp))
  have hint : MeasureTheory.Integrable g P := hmem.integrable (by norm_num)
  have hsq : MeasureTheory.Integrable (fun ω => g ω ^ 2) P := by
    have hmul := hmem.integrable_mul hmem
    have hfun : (fun ω => g ω ^ 2) = g * g := by
      funext ω
      simp [pow_two]
    rw [hfun]
    exact hmul
  have hsqnn : ∀ ω : Ω, (0 : ℝ) ≤ g ω ^ 2 := fun ω => sq_nonneg _
  have hkey : ENNReal.ofReal (∫ ω, g ω ^ 2 ∂P) ≤ ENNReal.ofReal V := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsq
      (Filter.Eventually.of_forall hsqnn)]
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hle
    exact (LevyStochCalc.Brownian.Ito.sq_enn_nnnorm_eq_ofReal_sq (g ω)).symm
  refine ⟨hint, _root_.Prove2MeSourceProof.h_33cc866be12cedca71971a8f hint.abs hsq ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hV0).mp hkey
section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Formula

end LevyStochCalc.Brownian.Ito


