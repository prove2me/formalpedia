-- Prove2me | Definitions.Def_SourceProof_a7edd00a4084ca3841211aa5
-- name    : SourceProof_a7edd00a4084ca3841211aa5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:11:36.797901+00:00
-- url     : https://prove2.me/theorems/a42527d6-09d4-45c0-876d-fbd5e775b50a
-- title:
--   LevyStochCalc source module: SourceProof_a7edd00a4084ca3841211aa5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentRestrict` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
import Definitions.Def_SourceProof_f876f8c69608bcdca53a63e6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Restriction of a simple predictable integrand to `(a, b]`

An adapted simple integrand `G` multiplied by the simple integrand `1_{(a, b]}` on their common
refinement is again an adapted simple integrand: its evaluation is `1_{(a, b]}·G`, its
coefficients vanish on every tile not contained in `(a, b]` and stay bounded by any bound on the
coefficients of `G`, and the variance budget of that per-tile bound is at most `C²(b − a)`.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_a7edd00a4084ca3841211aa5
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
      ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
          ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0) := by
  classical
  obtain ⟨T₃, Q, hQadapt, hQeval, -⟩ :=
    _root_.Prove2MeSourceProof.h_f876f8c69608bcdca53a63e6 W ℱ G (LevyStochCalc.Brownian.Ito.stepIocGen Ω ha hab) h_adapt
      (LevyStochCalc.Brownian.Ito.stepIocGen_adapt ℱ ha hab)
  have hQeval' : ∀ s ω, Q.eval s ω
      = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω := by
    intro s ω
    rw [hQeval s ω, LevyStochCalc.Brownian.Ito.stepIocGen_eval ha hab, mul_comm]
  refine ⟨T₃, Q, hQadapt, hQeval', fun j ω => ?_⟩
  have hlt : Q.partition j.castSucc < Q.partition j.succ :=
    Q.partition_strictMono Fin.castSucc_lt_succ
  by_cases hin : a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b
  · rw [if_pos hin]
    have hs : Q.partition j.castSucc < Q.partition j.succ
        ∧ Q.partition j.succ ≤ Q.partition j.succ := ⟨hlt, le_rfl⟩
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' _ ω, abs_mul]
    have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)| ≤ 1 := by
      by_cases hm : Q.partition j.succ ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hm]; norm_num
      · rw [Set.indicator_of_notMem hm]; norm_num
    calc |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)|
          * |G.eval (Q.partition j.succ) ω|
        ≤ 1 * C := by
          exact mul_le_mul h1 (G.abs_eval_le hC0 hC _ ω) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [if_neg hin]
    -- pick a time in the tile that lies outside `(a, b]`
    obtain ⟨s, hs, hsout⟩ : ∃ s : ℝ, (Q.partition j.castSucc < s ∧ s ≤ Q.partition j.succ)
        ∧ s ∉ Set.Ioc a b := by
      by_cases hb : Q.partition j.succ ≤ b
      · have hna : Q.partition j.castSucc < a := by
          by_contra hcon
          exact hin ⟨not_lt.mp hcon, hb⟩
        refine ⟨min a (Q.partition j.succ), ⟨lt_min hna hlt, min_le_right _ _⟩, ?_⟩
        exact fun hm => absurd (Set.mem_Ioc.mp hm).1 (not_lt.mpr (min_le_left _ _))
      · refine ⟨Q.partition j.succ, ⟨hlt, le_rfl⟩, ?_⟩
        exact fun hm => hb (Set.mem_Ioc.mp hm).2
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' s ω, Set.indicator_of_notMem hsout, zero_mul,
      abs_zero]
end LevyStochCalc.Brownian.Ito


