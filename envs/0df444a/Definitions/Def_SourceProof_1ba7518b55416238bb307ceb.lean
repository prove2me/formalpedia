-- Prove2me | Definitions.Def_SourceProof_1ba7518b55416238bb307ceb
-- name    : SourceProof_1ba7518b55416238bb307ceb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:19.749588+00:00
-- url     : https://prove2.me/theorems/293b95f3-f7b0-4795-a6b7-809742d01931
-- title:
--   LevyStochCalc source module: SourceProof_1ba7518b55416238bb307ceb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` comes from the `LevyStochCalc.Brownian.ItoQuadVarRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000
import Definitions.Def_SourceProof_12a9610fb78426e446f445d9
import Definitions.Def_SourceProof_33cc866be12cedca71971a8f

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

theorem _root_.Prove2MeSourceProof.h_1ba7518b55416238bb307ceb
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * quadVarIncrement W ℱ hℱ H hm hp hq (unifGrid T m i)
              (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2)) := by
  have hgadapt : ∀ k : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ.rightCont (LevyStochCalc.Brownian.Ito.unifGrid T m k)) (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m k) ω)) := fun k =>
    hφc.comp_stronglyMeasurable ((h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m k)).mono (ℱ.le_rightCont _))
  have hquad := _root_.Prove2MeSourceProof.h_12a9610fb78426e446f445d9 W ℱ hℱ H hm hp hq hC0 hCH
    (LevyStochCalc.Brownian.Ito.unifGrid T m) (by simp) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0)
    (fun k ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m k) ω)) hgadapt hKφ0 (fun k ω => hφbd _) m
  have hmesh : ∑ i ∈ Finset.range m, (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) - LevyStochCalc.Brownian.Ito.unifGrid T m i) ^ 2
      = (m : ℝ) * (T / (m : ℝ)) ^ 2 := by
    simp_rw [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hmesh] at hquad
  have hζmem : ∀ k : ℕ, MeasureTheory.MemLp (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq
      (LevyStochCalc.Brownian.Ito.unifGrid T m k) (LevyStochCalc.Brownian.Ito.unifGrid T m (k + 1))) 2 P := fun k =>
    LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m k)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 k)
  have hYmem : ∀ k : ℕ, MeasureTheory.MemLp (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m k) ω)
      * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m k)
          (LevyStochCalc.Brownian.Ito.unifGrid T m (k + 1)) ω) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul Kφ)
      ((hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m k))).aestronglyMeasurable.mul
        (hζmem k).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hsummem : MeasureTheory.MemLp (fun ω => ∑ i ∈ Finset.range m,
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
          (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) 2 P :=
    MeasureTheory.memLp_finsetSum _ fun i _ => hYmem i
  have hint1 : MeasureTheory.Integrable (fun ω => |∑ i ∈ Finset.range m,
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
          (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω|) P := (hsummem.integrable (by norm_num)).abs
  have hint2 : MeasureTheory.Integrable (fun ω => (∑ i ∈ Finset.range m,
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
          (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) ^ 2) P := by
    have hmul := hsummem.integrable_mul hsummem
    have hfun : (fun ω => (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
            (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) ^ 2)
        = (fun ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
          * fun ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i)
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω := by
      funext ω
      simp [pow_two]
    rw [hfun]
    exact hmul
  exact ⟨hsummem.integrable (by norm_num),
    _root_.Prove2MeSourceProof.h_33cc866be12cedca71971a8f hint1 hint2 hquad⟩
end QuadVarRiemann

end LevyStochCalc.Brownian.Ito


