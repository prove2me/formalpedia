-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000
-- name    : LevyStochCalc_Brownian_ItoPullOut_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:56:18.933908+00:00
-- url     : https://prove2.me/theorems/1aeb7b33-451a-4823-88a5-c6115765d363
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoPullOut
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoPullOut. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The simple integrand `V · 1_{(a, b]}`, for `0 < a < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
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
  ξ := ![fun _ => 0, V]
  ξ_bounded := by
    intro i
    fin_cases i
    · exact ⟨0, fun ω => by norm_num⟩
    · exact hVb
  ξ_measurable := by
    intro i
    fin_cases i
    · exact measurable_const
    · exact hVm
/-- The simple integrand `V · 1_{(0, b]}`, for `0 < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![V]
  ξ_bounded := by intro i; fin_cases i; exact hVb
  ξ_measurable := by intro i; fin_cases i; exact hVm
theorem stepIocMul_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).eval s ω = V ω * indIoc Ω a b ω s := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  change _ = V ω * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
  split_ifs <;> simp_all [Set.indicator, Set.mem_Ioc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
theorem stepIocMul₀_eval {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).eval s ω = V ω * indIoc Ω 0 b ω s := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![V] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  change _ = V ω * (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s
  split_ifs <;> simp_all [Set.indicator, Set.mem_Ioc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
theorem stepIocMul_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    ∀ i : Fin (stepIocMul Ω ha hab V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul Ω ha hab V hVb hVm).partition i.castSucc))
      ((stepIocMul Ω ha hab V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  · exact MeasureTheory.stronglyMeasurable_const
  · exact hVa
theorem stepIocMul₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ 0) V) :
    ∀ i : Fin (stepIocMul₀ Ω hb V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul₀ Ω hb V hVb hVm).partition i.castSucc))
      ((stepIocMul₀ Ω hb V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  exact hVa
theorem stepIocMul_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min a t) ω) := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp
theorem stepIocMul₀_integralAgainst {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min 0 t) ω) := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 1, (![V] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp
section PullOut

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end PullOut

end LevyStochCalc.Brownian.Ito


