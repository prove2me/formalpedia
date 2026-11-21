-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityMarkSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:38:57.654362+00:00
-- url     : https://prove2.me/theorems/68331e1f-4ae5-4b58-adb5-45917c10aedc
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityMarkSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityMarkSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Reference-intensity of a time-mark box factorises.** For `0 ≤ a`,
`ν̂((a,b]×A) = ofReal(b−a)·ν(A)` (`referenceIntensity = (volume.restrict (Ici 0)).prod ν`
and `(a,b] ⊆ [0,∞)`). -/
lemma referenceIntensity_Ioc_prod_eq
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} (ha : 0 ≤ a) {A : Set E} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
      = ENNReal.ofReal (b - a) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Set.Ioc a b ⊆ Set.Ici 0 from fun x hx => ha.trans hx.1.le), Real.volume_Ioc]
/-- **Mark-space `L²` of a finite mark-simple function.** For arbitrary marks `B k`
(finite `ν`) and reals `c k`,
`∫_E (∑ₖ cₖ·𝟙_{Bₖ}(e))² dν = ∑ₖ ∑ₖ' cₖ·cₖ'·ν(Bₖ∩Bₖ')`. The mark-direction analogue of
`markSum_sq_sametime`; underlies the Tonelli bridge from the isometry sum-form to the
integrand `L²` norm. -/
lemma mark_sq_integral
    {ν : Measure E} [SigmaFinite ν] {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤) (c : Fin K → ℝ) :
    ∫ e, (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 ∂ν
      = ∑ k : Fin K, ∑ k' : Fin K, c k * c k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hexp : (fun e => (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
      = fun e => ∑ k : Fin K, ∑ k' : Fin K,
          (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
    funext e
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
  have hintg : ∀ k k', MeasureTheory.Integrable
      (fun e => (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e) ν :=
    fun k k' => (((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k')))).const_mul _
  rw [hexp, MeasureTheory.integral_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => hintg k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hintg k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator_const (1 : ℝ) (hinterm k k'),
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]
end LevyStochCalc.Poisson.Compensated


