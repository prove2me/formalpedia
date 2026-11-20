-- Prove2me | Definitions.Def_SourceProof_51f09268151a2e0d175471a2
-- name    : SourceProof_51f09268151a2e0d175471a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:08:50.910183+00:00
-- url     : https://prove2.me/theorems/0d776957-b2e6-437b-8b85-73c6902280c5
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.BrownianMotion.hasLaw_increment
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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

namespace BrownianMotion


theorem _root_.Prove2MeSourceProof.h_51f09268151a2e0d175471a2 (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω ↦ W.W (t : ℝ) ω - W.W (s : ℝ) ω) (gaussianReal 0 (t - s)) P := by
  rcases eq_or_lt_of_le hst with h | h
  · subst h
    have hfun : (fun ω ↦ W.W (s : ℝ) ω - W.W (s : ℝ) ω) = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; ring
    rw [tsub_self, gaussianReal_zero_var, hfun]
    exact ⟨measurable_const.aemeasurable, by simp⟩
  · refine ⟨((W.measurable_eval _).sub (W.measurable_eval _)).aemeasurable, ?_⟩
    rw [W.increment_gaussian s.coe_nonneg (NNReal.coe_lt_coe.2 h)]
    congr 1
    apply NNReal.coe_injective
    change (t : ℝ) - (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub hst]
end BrownianMotion

end LevyStochCalc.Brownian


