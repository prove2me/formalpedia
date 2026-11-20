-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_MathlibBridge_F001
-- name    : LevyStochCalc_Brownian_MathlibBridge_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:28:33.866325+00:00
-- url     : https://prove2.me/theorems/0674f723-420e-4ba2-ab55-5afdc2c065c7
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.MathlibBridge
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.MathlibBridge in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MathlibBridge_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion in the sense of Mathlib

A `BrownianMotion P` in the sense of `LevyStochCalc.Brownian.Construction`, restricted along the
coercion `ℝ≥0 → ℝ`, is a Brownian motion in the sense of `ProbabilityTheory.IsBrownianReal`: its
value at time `t` has law `gaussianReal 0 t`, its increments along a monotone tuple are mutually
independent, and its paths are almost surely continuous. Mutual independence of the increments
comes from the σ-algebra field `BrownianMotion.joint_increment_independent` through
`iIndep_of_indep_biSup_lt`, a chain criterion for mutual independence of a family of σ-algebras
indexed by a linear order.

## Main statements

* `iIndep_of_indep_biSup_lt` — a family of σ-algebras indexed by a linear order is mutually
  independent as soon as each member is independent of the supremum of its predecessors.
* `BrownianMotion.hasLaw_eval`, `BrownianMotion.hasLaw_increment` — the marginal laws.
* `BrownianMotion.hasIndepIncrements` — mutual independence of the increments.
* `BrownianMotion.isPreBrownianReal`, `BrownianMotion.isBrownianReal`,
  `BrownianMotion.isGaussianProcess` — the Mathlib predicates.
* `BrownianMotion.ofIsPreBrownianReal_w_ae_eq` — the round trip through
  `BrownianMotion.ofIsPreBrownianReal` recovers the paths at nonnegative times.
-/

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace BrownianMotion

/-- A Brownian motion, read on nonnegative times, has independent increments. -/
theorem hasIndepIncrements (W : BrownianMotion P) :
    HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P := by
  intro n t ht
  refine (iIndepFun_iff_iIndep _ _ _).2 (iIndep_of_indep_biSup_lt fun i ↦ ?_)
  have hab : ((t i.castSucc : ℝ)) ≤ (t i.succ : ℝ) :=
    NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ i))
  have hsub : (⨆ j < i, MeasurableSpace.comap
        (fun ω ↦ W.W (t j.succ : ℝ) ω - W.W (t j.castSucc : ℝ) ω) inferInstance)
      ≤ ⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
        MeasurableSpace.comap (W.W q) inferInstance := by
    refine iSup₂_le fun j hj ↦ ?_
    have hji : (j : ℕ) < (i : ℕ) := hj
    have hjs : ((t j.succ : ℝ)) ≤ (t i.castSucc : ℝ) := by
      refine NNReal.coe_le_coe.2 (ht ?_)
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hjc : ((t j.castSucc : ℝ)) ≤ (t i.castSucc : ℝ) :=
      le_trans (NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ j))) hjs
    have hmem : ∀ {r : ℝ}, r ≤ (t i.castSucc : ℝ) →
        Measurable[⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
          MeasurableSpace.comap (W.W q) inferInstance] (W.W r) := fun {r} hr ↦
      Measurable.of_comap_le (le_iSup₂ (f := fun q (_ : q ∈ Set.Iic ((t i.castSucc : ℝ))) ↦
        MeasurableSpace.comap (W.W q) inferInstance) r hr)
    exact Measurable.comap_le ((hmem hjs).sub (hmem hjc))
  rcases eq_or_lt_of_le hab with hEq | hLt
  · have hconst : (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω)
        = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; rw [hEq]; ring
    have hbot : MeasurableSpace.comap
        (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω) inferInstance
        = (⊥ : MeasurableSpace Ω) := by
      rw [hconst]; exact MeasurableSpace.comap_const 0
    exact indep_of_indep_of_le_right (indep_bot_right _) (le_of_eq hbot)
  · exact indep_of_indep_of_le_left
      (W.joint_increment_independent (t i.castSucc).coe_nonneg hLt) hsub
/-- A Brownian motion, read on nonnegative times, is a pre-Brownian motion. -/
theorem isPreBrownianReal (W : BrownianMotion P) :
    IsPreBrownianReal (fun t : ℝ≥0 ↦ W.W t) P :=
  HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ W.hasLaw_eval t) W.hasIndepIncrements
/-- A Brownian motion, read on nonnegative times, is a Brownian motion in the sense of
`ProbabilityTheory.IsBrownianReal`. -/
theorem isBrownianReal (W : BrownianMotion P) :
    IsBrownianReal (fun t : ℝ≥0 ↦ W.W t) P where
  toIsPreBrownianReal := W.isPreBrownianReal
  cont := by
    filter_upwards [W.continuous_paths] with ω hω
    exact hω.comp NNReal.continuous_coe
/-- A Brownian motion, read on nonnegative times, is a Gaussian process. -/
theorem isGaussianProcess (W : BrownianMotion P) :
    IsGaussianProcess (fun t : ℝ≥0 ↦ W.W t) P :=
  W.isPreBrownianReal.isGaussianProcess
/-- The Brownian motion rebuilt from `BrownianMotion.isPreBrownianReal` has paths
`t ↦ W t - W 0` at nonnegative times. -/
theorem ofIsPreBrownianReal_w_apply (W : BrownianMotion P)
    (hcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ W.W u ω) {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    (BrownianMotion.ofIsPreBrownianReal W.isPreBrownianReal
      (fun u ↦ W.measurable_eval u) hcont).W r ω = W.W r ω - W.W 0 ω := by
  simp [BrownianMotion.ofIsPreBrownianReal, realTime, Real.coe_toNNReal r hr]
/-- The Brownian motion rebuilt from `BrownianMotion.isPreBrownianReal` is almost surely equal to
the original one at each nonnegative time. -/
theorem ofIsPreBrownianReal_w_ae_eq (W : BrownianMotion P)
    (hcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ W.W u ω) {r : ℝ} (hr : 0 ≤ r) :
    (BrownianMotion.ofIsPreBrownianReal W.isPreBrownianReal
      (fun u ↦ W.measurable_eval u) hcont).W r =ᵐ[P] W.W r := by
  filter_upwards [W.initial_zero] with ω hω
  rw [ofIsPreBrownianReal_w_apply W hcont hr ω, hω, sub_zero]
end BrownianMotion

end LevyStochCalc.Brownian


