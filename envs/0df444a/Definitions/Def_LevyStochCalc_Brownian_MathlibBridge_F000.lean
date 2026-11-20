-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_MathlibBridge_F000
-- name    : LevyStochCalc_Brownian_MathlibBridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:25:41.734082+00:00
-- url     : https://prove2.me/theorems/f1220ba4-7cbe-411c-a43e-e93a3249f5d1
-- title:
--   Source declarations: LevyStochCalc.Brownian.MathlibBridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.MathlibBridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Existence_F000

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

/-- A family of σ-algebras indexed by a linear order is mutually independent as soon as each
member is independent of the supremum of the members of strictly smaller index. -/
theorem iIndep_of_indep_biSup_lt {ι : Type*} [LinearOrder ι] {m : ι → MeasurableSpace Ω}
    (h : ∀ i, Indep (⨆ j < i, m j) (m i) P) : iIndep m P := by
  classical
  have key : ∀ (S : Finset ι) (f : ι → Set Ω), (∀ i ∈ S, MeasurableSet[m i] (f i)) →
      P (⋂ i ∈ S, f i) = ∏ i ∈ S, P (f i) := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro f _; simp
    | insert a s hlt ih =>
      intro f hf
      have hane : a ∉ s := fun ha ↦ lt_irrefl a (hlt a ha)
      have hfs : ∀ i ∈ s, MeasurableSet[m i] (f i) := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hmeas : MeasurableSet[⨆ j < a, m j] (⋂ i ∈ s, f i) :=
        Finset.measurableSet_biInter (α := Ω) (m := ⨆ j < a, m j) s fun i hi ↦
          le_iSup₂ (f := fun j (_ : j < a) ↦ m j) i (hlt i hi) _ (hfs i hi)
      rw [Finset.set_biInter_insert, Finset.prod_insert hane,
        (Indep_iff _ _ _).1 (h a).symm _ _ (hf a (Finset.mem_insert_self a s)) hmeas,
        ih f hfs]
  rw [iIndep_iff]
  intro S f hf
  exact key S f hf
namespace BrownianMotion

/-- The value of a Brownian motion at a nonnegative time `t` has law `gaussianReal 0 t`. -/
theorem hasLaw_eval (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (W.W (t : ℝ)) (gaussianReal 0 t) P := by
  have hzero : (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) =ᵐ[P] W.W (t : ℝ) := by
    filter_upwards [W.initial_zero] with ω hω using by simp [hω]
  rcases eq_or_lt_of_le t.coe_nonneg with h | h
  · have ht0 : t = 0 := NNReal.coe_injective h.symm
    subst ht0
    rw [gaussianReal_zero_var]
    refine HasLaw.congr (X := fun _ : Ω ↦ (0 : ℝ)) ⟨measurable_const.aemeasurable, by simp⟩ ?_
    filter_upwards [W.initial_zero] with ω hω using by simpa using hω
  · have hmap : P.map (fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω) = gaussianReal 0 t := by
      rw [W.increment_gaussian (s := 0) (t := (t : ℝ)) le_rfl h]
      congr 1
      apply NNReal.coe_injective
      change (t : ℝ) - 0 = (t : ℝ)
      rw [sub_zero]
    exact HasLaw.congr (X := fun ω ↦ W.W (t : ℝ) ω - W.W 0 ω)
      ⟨((W.measurable_eval _).sub (W.measurable_eval 0)).aemeasurable, hmap⟩ hzero.symm
end BrownianMotion

end LevyStochCalc.Brownian


