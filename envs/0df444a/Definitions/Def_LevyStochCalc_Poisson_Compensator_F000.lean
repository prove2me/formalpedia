-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
-- name    : LevyStochCalc_Poisson_Compensator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:15:39.818359+00:00
-- url     : https://prove2.me/theorems/36d30a60-fe6b-4260-893e-1552d2a1b1fa
-- title:
--   Source declarations: LevyStochCalc.Poisson.Compensator
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Compensator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001
import Definitions.Def_SourceProof_9d62612e2dce26cbc374ccfb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The reference intensity as compensator on a finite-activity window

On a predictable rectangle the count of the Poisson random measure is independent of the past
event carried by the rectangle, so its mean factorises as the probability of that event times
the intensity of the time–mark part. The sets on which the two mean occupations agree form a
Dynkin system — complements by subtracting from the finite occupation of the window, countable
disjoint unions by monotone convergence — so they agree on every predictable set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- A time interval times a mark set of finite intensity has finite reference intensity. -/
theorem referenceIntensity_Ioc_prod_ne_top' {B : Set E} (hBν : ν B ≠ ⊤) (r q : ℝ) :
    referenceIntensity ν (Set.Ioc r q ×ˢ B) ≠ ⊤ := by
  rw [referenceIntensity, Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hBν
  rw [Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)
section Rectangle

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **Independence factorises the mean count of a future rectangle over a past event.** -/
theorem setLIntegral_count_eq (hℱ : IsPoissonFiltration N ℱ) {r q : ℝ} (hr : 0 ≤ r)
    {F : Set Ω} (hF : MeasurableSet[ℱ r] F) {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤) :
    ∫⁻ ω in F, N.N ω (Set.Ioc r q ×ˢ B) ∂P
      = P F * referenceIntensity ν (Set.Ioc r q ×ˢ B) := by
  rcases le_or_gt q r with hqr | hrq
  · have hempty : Set.Ioc r q = (∅ : Set ℝ) := Set.Ioc_eq_empty (not_lt.mpr hqr)
    simp [hempty]
  · have hmeas : Measurable fun ω => N.N ω (Set.Ioc r q ×ˢ B) :=
      N.measurable_eval (measurableSet_Ioc.prod hB)
    have hfin : referenceIntensity ν (Set.Ioc r q ×ˢ B) ≠ ⊤ :=
      referenceIntensity_Ioc_prod_ne_top' hBν r q
    have hidp := hℱ.indep hr hrq hB hBν
    have hmapeq : (P.restrict F).map (fun ω => N.N ω (Set.Ioc r q ×ˢ B))
        = P F • P.map (fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by
      ext U hU
      rw [Measure.map_apply hmeas hU, Measure.restrict_apply (hmeas hU), Measure.smul_apply,
        Measure.map_apply hmeas hU, smul_eq_mul, Set.inter_comm]
      exact (Indep_iff _ _ _).mp hidp F ((fun ω => N.N ω (Set.Ioc r q ×ˢ B)) ⁻¹' U) hF
        ⟨U, hU, rfl⟩
    calc ∫⁻ ω in F, N.N ω (Set.Ioc r q ×ˢ B) ∂P
        = ∫⁻ x, x ∂((P.restrict F).map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) :=
          (lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' hmeas).symm
      _ = ∫⁻ x, x ∂(P F • P.map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by rw [hmapeq]
      _ = P F * ∫⁻ x, x ∂(P.map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = P F * ∫⁻ ω, N.N ω (Set.Ioc r q ×ˢ B) ∂P := by
          rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' hmeas]
      _ = P F * referenceIntensity ν (Set.Ioc r q ×ˢ B) := by
          rw [_root_.Prove2MeSourceProof.h_9d62612e2dce26cbc374ccfb N
            (measurableSet_Ioc.prod hB) hfin]
end Rectangle

section Window

/-- The count of the slice of a set of the time–mark space, inside a window. -/
noncomputable def sliceCount (N : PoissonRandomMeasure P ν) (R : Set (ℝ × E))
    (S : Set (Ω × ℝ × E)) (ω : Ω) : ℝ≥0∞ := N.N ω (Prod.mk ω ⁻¹' S ∩ R)
/-- The reference intensity of the slice of a set of the time–mark space, inside a window. -/
noncomputable def sliceIntensity (ν : Measure E) (R : Set (ℝ × E)) (S : Set (Ω × ℝ × E))
    (ω : Ω) : ℝ≥0∞ := referenceIntensity ν (Prod.mk ω ⁻¹' S ∩ R)
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Window

end LevyStochCalc.Poisson


