-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F001
-- name    : LevyStochCalc_Brownian_ItoFormulaGrid_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:25.156742+00:00
-- url     : https://prove2.me/theorems/0660330d-daad-49ac-b5e4-3f3e1e7899c2
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFormulaGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFormulaGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
import Definitions.Def_SourceProof_4ef3e5b73189336215f644cf

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

/-- The simple integrand on the uniform grid of `[0, T]` with the given cell coefficients. -/
noncomputable def SimplePredictable.ofUnifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) : SimplePredictable Ω T where
  N := m
  partition := fun i => unifGrid T m (i : ℕ)
  partition_zero := by simp
  partition_le_T := le_of_eq (by simpa using unifGrid_self (T := T) hm)
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simpa using unifGrid_lt_succ hT hm (i : ℕ)
  ξ := ξ
  ξ_bounded := hbdd
  ξ_measurable := hmeas
@[simp] theorem SimplePredictable.ofUnifGrid_partition {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin (m + 1)) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i = unifGrid T m (i : ℕ) := rfl
@[simp] theorem SimplePredictable.ofUnifGrid_xi {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i = ξ i := rfl
theorem SimplePredictable.ofUnifGrid_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    ∀ i : Fin (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i.castSucc))
        ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i) := hadapt
/-- The grid integrand evaluates to the cell coefficient on each cell. -/
theorem SimplePredictable.ofUnifGrid_eval {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) {s : ℝ}
    (hs : unifGrid T m (i : ℕ) < s ∧ s ≤ unifGrid T m ((i : ℕ) + 1)) (ω : Ω) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval s ω = ξ i ω :=
  (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval_of_mem_Ioc i hs ω
section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **The third absolute moments of the Itô-integral increments across a uniform grid sum to
`O(m^{-1/2})`.** -/
theorem sum_integral_abs_sub_pow_three_le {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m,
        ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
      ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hstep : ∀ i : ℕ, unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) :=
    unifGrid_succ_sub hm0
  have hK0 : (0 : ℝ) ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 := by
    have := gaussianFourthMoment_nonneg
    have h1 : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    have h2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
    linarith
  have hterm : ∀ i ∈ Finset.range m,
      ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))) := by
    intro i _
    have h := (_root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf W ℱ hℱ H hm hp hq hC0 hCH
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)).2
    rwa [hstep i] at h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  calc (m : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))))
      = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ))) := by ring
    _ = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
        rw [hTm]
    _ ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) :=
        le_rfl
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

end ItoIncrement

end LevyStochCalc.Brownian.Ito


