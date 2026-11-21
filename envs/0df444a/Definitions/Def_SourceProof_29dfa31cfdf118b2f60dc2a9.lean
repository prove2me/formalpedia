-- Prove2me | Definitions.Def_SourceProof_29dfa31cfdf118b2f60dc2a9
-- name    : SourceProof_29dfa31cfdf118b2f60dc2a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:48:28.242548+00:00
-- url     : https://prove2.me/theorems/f4ba719d-8e2e-446f-a249-d666e881977a
-- title:
--   LevyStochCalc source module: SourceProof_29dfa31cfdf118b2f60dc2a9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stepIoc₀_eval` comes from the `LevyStochCalc.Brownian.ItoAlgebraAssociativity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001

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

theorem _root_.Prove2MeSourceProof.h_29dfa31cfdf118b2f60dc2a9 {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hb).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    exact if_neg h
end LevyStochCalc.Brownian.Ito


