-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001
-- name    : LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:46:09.861074+00:00
-- url     : https://prove2.me/theorems/8e604378-ae4e-4510-91ca-b849e7d78bae
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

/-- The simple integrand `1_{(a, b]}`, for `0 < a < b`. -/
noncomputable def stepIoc (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, fun _ => 1]
  ξ_bounded := by intro i; fin_cases i <;> exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i <;> exact measurable_const
/-- The simple integrand `1_{(0, b]}`, for `0 < b`. -/
noncomputable def stepIoc₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![fun _ => 1]
  ξ_bounded := by intro i; fin_cases i; exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i; exact measurable_const
theorem stepIoc_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  classical
  have hrw : (stepIoc Ω ha hab).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  split_ifs <;> simp_all [Set.indicator, Set.mem_Ioc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
end LevyStochCalc.Brownian.Ito


