-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
-- name    : LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:16.0202+00:00
-- url     : https://prove2.me/theorems/3f4ce9bb-2779-418e-aba1-23808f695fa6
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrementMomentRestrict
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrementMomentRestrict. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
import Definitions.Def_SourceProof_29dfa31cfdf118b2f60dc2a9

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

/-- The simple integrand `1_{(a, b]}` for `0 ≤ a < b`. -/
noncomputable def stepIocGen (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SimplePredictable Ω b :=
  if h : 0 < a then stepIoc Ω h hab else stepIoc₀ Ω (lt_of_le_of_lt ha hab)
@[simp] theorem stepIocGen_eval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIocGen Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h, stepIoc_eval]
  · rw [dif_neg h]
    have ha0 : a = 0 := le_antisymm (not_lt.mp h) ha
    subst ha0
    exact _root_.Prove2MeSourceProof.h_29dfa31cfdf118b2f60dc2a9 _ s ω
theorem stepIocGen_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∀ i : Fin (stepIocGen Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocGen Ω ha hab).partition i.castSucc)) ((stepIocGen Ω ha hab).ξ i) := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h]; exact stepIoc_adapt ℱ h hab
  · rw [dif_neg h]; exact stepIoc₀_adapt ℱ _
/-- A simple integrand whose coefficients vanish on every tile not contained in `(a, b]` has the
same elementary integral at every time past `b`. -/
theorem SimplePredictable.simpleIntegral_eq_of_support
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {a b : ℝ}
    (hz : ∀ (j : Fin H.N) (ω : Ω),
      ¬(a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b) → H.ξ j ω = 0)
    {t : ℝ} (hbt : b ≤ t) (ω : Ω) : simpleIntegral W H t ω = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum]
  unfold simpleIntegral
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b
  · have h1 : H.partition j.succ ≤ t := hj.2.trans hbt
    have h2 : H.partition j.castSucc ≤ t :=
      ((H.partition_strictMono Fin.castSucc_lt_succ).le).trans h1
    rw [min_eq_left h1, min_eq_left h2]
  · rw [hz j ω hj, zero_mul, zero_mul]
end LevyStochCalc.Brownian.Ito


