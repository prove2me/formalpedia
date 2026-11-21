-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002
-- name    : LevyStochCalc_Brownian_ItoFormulaGrid_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:29:29.356435+00:00
-- url     : https://prove2.me/theorems/715478f2-3e16-4105-9f70-7c47baeda483
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFormulaGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFormulaGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F001
import Definitions.Def_SourceProof_2533e0a246989e508bdd4060

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

/-- **The grid step weight is uniformly close to a uniformly continuous weight.** If the cell
coefficients are the weight frozen at the left endpoints, the step process differs from the
weight by at most the weight's modulus of continuity at the mesh. -/
theorem abs_ofUnifGrid_eval_sub_le {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (g : Ω → ℝ → ℝ) {ε : ℝ}
    (hξg : ∀ (i : Fin m) (ω : Ω), ξ i ω = g ω (unifGrid T m (i : ℕ)))
    (hmod : ∀ ω : Ω, ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| ≤ T / (m : ℝ) → |g ω x - g ω y| ≤ ε)
    (ω : Ω) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    |(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω - g ω s| ≤ ε := by
  obtain ⟨i, hi, hlt, hle⟩ := _root_.Prove2MeSourceProof.h_2533e0a246989e508bdd4060 hT hm0 hs.1 hs.2
  have heval : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω = ξ ⟨i, hi⟩ ω :=
    SimplePredictable.ofUnifGrid_eval hT hm0 ξ hbdd hmeas ⟨i, hi⟩ ⟨hlt, hle⟩ ω
  rw [heval, hξg ⟨i, hi⟩ ω]
  refine hmod ω _ ⟨unifGrid_nonneg hT.le m i, unifGrid_le hT.le hi.le hm0⟩ s
    ⟨hs.1.le, hs.2⟩ ?_
  have hstep : unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := unifGrid_succ_sub hm0 i
  rw [abs_of_nonpos (by linarith : unifGrid T m i - s ≤ 0)]
  linarith
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


