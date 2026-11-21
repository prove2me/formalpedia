-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
-- name    : LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:46:57.014294+00:00
-- url     : https://prove2.me/theorems/257fc490-c121-48d9-807a-20213fb64d2b
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraAssociativity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraAssociativity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Associativity and locality of the `L²` Brownian Itô integral

Summing the increments of the `L²` Itô integral of a process `H` against the coefficients of a
simple integrand `G` gives the `L²` Itô integral of the product `G · H`; specialising to the step
integrands `1_{(a, b]}` identifies the `L²` Itô integral of an integrand restricted to `(a, b]`
with the increment of the integral of the unrestricted integrand across `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

private lemma eLpNorm_mul_le_of_bound {P : Measure Ω} {c g : Ω → ℝ} {M : ℝ}
    (hM : ∀ ω, |c ω| ≤ M) :
    MeasureTheory.eLpNorm (fun ω => c ω * g ω) 2 P
      ≤ (‖M‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm g 2 P := by
  have hsm : (fun ω => M * g ω) = (M • g : Ω → ℝ) := by funext ω; simp
  refine le_trans (MeasureTheory.eLpNorm_mono (g := fun ω => M * g ω) fun ω => ?_) ?_
  · have hM0 : 0 ≤ M := (abs_nonneg (c ω)).trans (hM ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM ω) (abs_nonneg _)
  · rw [hsm]; exact MeasureTheory.eLpNorm_const_smul_le
section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Associativity

end LevyStochCalc.Brownian.Ito


