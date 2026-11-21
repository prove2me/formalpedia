-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F000
-- name    : LevyStochCalc_Poisson_SimpleProfile_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:29:57.745189+00:00
-- url     : https://prove2.me/theorems/4136382f-bdbe-45d4-9749-d4f1ab8a5752
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The reference intensity of a step of the time axis times a mark set. -/
theorem referenceIntensity_Ioc_prod' (A : Set E) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    referenceIntensity ν (Set.Ioc a b ×ˢ A) = ENNReal.ofReal (b - a) * ν A := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  congr 1
  rw [show Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b from by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => ha.trans h.1.le]
  rw [Real.volume_Ioc]
/-- A simple mark profile: finitely many pairwise disjoint mark sets of finite intensity
carrying constant coefficients. -/
structure SimpleProfile (E : Type v) [MeasurableSpace E] (ν : Measure E) where
  /-- Number of mark sets. -/
  K : ℕ
  /-- The mark sets. -/
  B : Fin K → Set E
  B_measurable : ∀ k, MeasurableSet (B k)
  B_disjoint : Pairwise fun k l => Disjoint (B k) (B l)
  B_finite : ∀ k, ν (B k) ≠ ⊤
  /-- The coefficients. -/
  c : Fin K → ℝ
namespace SimpleProfile

/-- The mark function carried by a simple profile. -/
noncomputable def toFun (G : SimpleProfile E ν) (e : E) : ℝ :=
  ∑ k, G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e
omit [SigmaFinite ν] in
/-- The function of a simple profile is measurable. -/
theorem measurable_toFun (G : SimpleProfile E ν) : Measurable G.toFun :=
  Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator (G.B_measurable k)).const_mul _
omit [SigmaFinite ν] in
/-- The function of a simple profile is square integrable. -/
theorem memLp_toFun (G : SimpleProfile E ν) : MemLp G.toFun 2 ν :=
  memLp_finsetSum _ fun k _ =>
    (memLp_indicator_const 2 (G.B_measurable k) (1 : ℝ) (Or.inr (G.B_finite k))).const_mul _
/-- The indicator of an intersection as a product of indicators. -/
private theorem indicator_one_mul {α : Type*} (s t : Set α) (e : α) :
    s.indicator (fun _ => (1 : ℝ)) e * t.indicator (fun _ => (1 : ℝ)) e
      = (s ∩ t).indicator (fun _ => (1 : ℝ)) e := by
  by_cases hs : e ∈ s <;> by_cases ht : e ∈ t <;> simp [hs, ht]
omit [SigmaFinite ν] in
/-- The pointwise product of the functions of two simple profiles, through the indicators of
the intersections of their mark sets. -/
theorem toFun_mul (G G' : SimpleProfile E ν) (e : E) :
    G.toFun e * G'.toFun e
      = ∑ k, ∑ l, G.c k * G'.c l * (G.B k ∩ G'.B l).indicator (fun _ => (1 : ℝ)) e := by
  rw [toFun, toFun, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← indicator_one_mul (G.B k) (G'.B l) e]
  ring
/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)

/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


