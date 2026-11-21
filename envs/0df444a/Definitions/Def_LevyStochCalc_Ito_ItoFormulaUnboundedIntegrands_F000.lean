-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
-- name    : LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:48:59.756903+00:00
-- url     : https://prove2.me/theorems/df59682b-fd12-4a0a-8559-59189fd60735
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of the clamped approximation of a vector Itô process

For a function whose first and second derivatives are bounded, the drift integrals, the quadratic
variation terms and the diffusion integrands built from the coefficients clamped at a level growing
to infinity converge to the ones built from the original coefficients: the drift and quadratic
variation terms pathwise, the diffusion integrands in energy on a bounded window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

omit [IsProbabilityMeasure P] in
/-- Clamping at a level that grows to infinity converges to the identity. -/
theorem tendsto_clampAt_comp {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i) (x : ℝ) :
    Filter.Tendsto (fun i => clampAt ((ns i : ℕ) : ℝ) x) Filter.atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  refine (clampAt_eq_self ?_).symm
  have hle : (N : ℝ) ≤ ((ns i : ℕ) : ℝ) := by exact_mod_cast le_trans hi (hge i)
  linarith [hN]
omit [IsProbabilityMeasure P] in
/-- For almost every path, an integrand with finite energy is square integrable on the window. -/
theorem ae_memLp_two_window {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MeasureTheory.MemLp (G ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hmG T) hqG.ne] with ω hω
  exact LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hmG) hω
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


