-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F001
-- name    : LevyStochCalc_Brownian_PRPGrid_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:08:47.704183+00:00
-- url     : https://prove2.me/theorems/97bbc2e8-d93d-4cd7-abc3-08459987fbc5
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F000
import Definitions.Def_SourceProof_3bb40c5e7df4a1af88374480

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation over a grid

Iterating the one-window statement over the cells of a grid: a square-integrable weight of mean
zero and orthogonal to every Itô integral is orthogonal to every character of the increments of a
Brownian motion along a grid.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Grid

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Grid

section Abel

end Abel

section Values

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

include hℱ in
/-- **Value characters along a grid.** A square-integrable weight of mean zero, orthogonal to
every Itô integral, is orthogonal to every character of the values of `W` at the points of a
grid. -/
theorem pairing_value_character_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → ℝ) (n : ℕ) (hlt : ∀ k, k < n → τ k < τ (k + 1)) :
    ∫ ω, Z ω * Complex.exp (((∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω : ℝ) : ℂ)
      * Complex.I) ∂P = 0 := by
  have hkey := pairing_gridCharacter_eq_zero hℱ0 hnull hτ0 hZm hZ2 hZp hZ0
    (fun k => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) n hlt
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [W.initial_zero] with ω hω
  have heq : (∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω)
      = ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j)
          * (W.W (τ (k + 1)) ω - W.W (τ k) ω) :=
    (_root_.Prove2MeSourceProof.h_3bb40c5e7df4a1af88374480 c (Wv := fun k => W.W (τ k) ω) (by rw [hτ0]; exact hω) n).symm
  rw [gridCharacter_eq_exp, heq]
end Values

end LevyStochCalc.Brownian.Ito


