-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFinsetSum_F000
-- name    : LevyStochCalc_Brownian_ItoFinsetSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:44.391474+00:00
-- url     : https://prove2.me/theorems/1158e696-2874-4b60-ad29-de72e404c753
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFinsetSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFinsetSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000
import Definitions.Def_SourceProof_f0468e0adacb16d8cd5e45b1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral over finite sums

Additivity and scaling give the negation, the difference and the sum over a finite index set.
The finite sum is stated existentially in the admissibility data of the summed integrand, which
the induction produces along with the identity.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`
* `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The square-integrability of an integrand transfers along an equality of integrands. -/
theorem energy_lt_top_congr {F₁ F₂ : Ω → ℝ → ℝ} (h : F₁ = F₂)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  subst h
  exact hq
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral negates with its integrand.** -/
theorem stochasticIntegralBrownian_neg {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmn : Measurable (Function.uncurry fun ω s => -H ω s))
    (hpn : Probability.ProgressivelyMeasurable ℱ fun ω s => -H ω s)
    (hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => -H ω s) hmn hpn hqn T
      =ᵐ[P] fun ω => -stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by
  have hfun : (fun (ω : Ω) (s : ℝ) => -H ω s) = fun ω s => (-1 : ℝ) * H ω s := by
    funext ω s
    ring
  have hmc : Measurable (Function.uncurry fun ω s => (-1 : ℝ) * H ω s) := hfun ▸ hmn
  have hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => (-1 : ℝ) * H ω s := hfun ▸ hpn
  have hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(-1 : ℝ) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := energy_lt_top_congr hfun hqn
  rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun hmn hpn hqn hmc hpc hqc T]
  filter_upwards [_root_.Prove2MeSourceProof.h_f0468e0adacb16d8cd5e45b1 W ℱ hℱ hm hp hq (-1) hmc hpc hqc hT]
    with ω hω
  rw [hω]
  ring
end LevyStochCalc.Brownian.Ito


