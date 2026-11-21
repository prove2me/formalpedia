-- Prove2me | Definitions.Def_SourceProof_a028c987115bc886420ad387
-- name    : SourceProof_a028c987115bc886420ad387
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:31:54.833717+00:00
-- url     : https://prove2.me/theorems/4ae41a41-ef09-4481-938a-dae484390eb4
-- title:
--   LevyStochCalc source module: SourceProof_a028c987115bc886420ad387
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` comes from the `LevyStochCalc.Brownian.ItoFormula` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRiemannIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F001
import Definitions.Def_SourceProof_d82a80578e51eb43ce3e150e
import Definitions.Def_SourceProof_e350717f59f1a5a72381b69b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Grid Riemann sums of the Itô integral

The weighted sum of the Itô integral's increments across a uniform grid is itself an Itô
integral — that of the grid's step weight against the integrand — and replacing the step weight
by a general one costs the `L²` distance between them times the bound on the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae` — the grid-weighted sum of increments as
  an Itô integral.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sum_unifGrid_sub_le` — that sum is `L²`-close to the
  Itô integral of the weight, with the weight's modulus of continuity as the rate.
* `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` — the second-order Taylor
  remainder along a uniform grid is `O(m^{-1/2})` in `L¹`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section GridSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end GridSum

section TaylorRemainder

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_a028c987115bc886420ad387
    {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) (bdrift : Ω → ℝ → ℝ)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => taylorRemainder f f' f''
        (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainder f f' f''
          (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
          + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
            * (T * Real.sqrt (T / (m : ℝ))))) := by
  have hX : ∀ i : ℕ, Measurable (LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i)) :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_itoProcess W ℱ hℱ H hm hp hq hX₀ hbm _
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hf'd : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hf'c : Continuous f' := hf'd.continuous
  have hf''c : Continuous f'' := by
    have hlip : LipschitzWith (Real.toNNReal K) f'' := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0]
      exact hf'' u v
    exact hlip.continuous
  -- the remainder is measurable
  have hR : Measurable fun ω => LevyStochCalc.taylorRemainder f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m := by
    unfold LevyStochCalc.taylorRemainder
    refine ((hfc.measurable.comp (hX m)).sub (hfc.measurable.comp (hX 0))).sub
      ((Finset.measurable_sum _ fun i _ => (hf'c.measurable.comp (hX i)).mul
          ((hX (i + 1)).sub (hX i))).add
        (Finset.measurable_sum _ fun i _ =>
          ((hf''c.measurable.comp (hX i)).mul (((hX (i + 1)).sub (hX i)).pow_const 2)).div_const 2))
  -- the pathwise Taylor bound
  have hptw : ∀ ω : Ω, |LevyStochCalc.taylorRemainder f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|
      ≤ K * ∑ i ∈ Finset.range m,
        |LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ^ 3 :=
    fun ω => LevyStochCalc.abs_taylorRemainder_le hK0 hf hf' hf'' _ m
  -- the increment splits into drift and martingale parts
  have hsplit : ∀ (i : ℕ) (ω : Ω),
      LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω
        = (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) := fun i ω =>
    LevyStochCalc.Brownian.Ito.itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le ω
  have hterm : ∀ i ∈ Finset.range m, MeasureTheory.Integrable (fun ω : Ω =>
      |LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ^ 3) P := by
    intro i _
    simp_rw [hsplit i]
    exact _root_.Prove2MeSourceProof.h_e350717f59f1a5a72381b69b W ℱ hℱ H hm hp hq hC0 hCH bdrift hbm hB0 hB
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
  have hsumint : MeasureTheory.Integrable (fun ω : Ω => K * ∑ i ∈ Finset.range m,
      |LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ hterm).const_mul K
  have hRint : MeasureTheory.Integrable (fun ω : Ω => |LevyStochCalc.taylorRemainder f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|) P := by
    refine hsumint.mono hR.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : MeasureTheory.Integrable (fun ω : Ω => LevyStochCalc.taylorRemainder f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |LevyStochCalc.taylorRemainder f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, K * ∑ i ∈ Finset.range m,
          |LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ^ 3 ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = K * ∑ i ∈ Finset.range m, ∫ ω,
          |LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hterm]
    _ ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        simp_rw [hsplit]
        exact _root_.Prove2MeSourceProof.h_d82a80578e51eb43ce3e150e W ℱ hℱ H hm hp hq hC0 hCH bdrift hbm
          hB0 hB hT hm0
end TaylorRemainder

end LevyStochCalc.Brownian.Ito


