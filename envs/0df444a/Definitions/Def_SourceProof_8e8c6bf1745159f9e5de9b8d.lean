-- Prove2me | Definitions.Def_SourceProof_8e8c6bf1745159f9e5de9b8d
-- name    : SourceProof_8e8c6bf1745159f9e5de9b8d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:32:18.785563+00:00
-- url     : https://prove2.me/theorems/af65d1da-1d65-4a8a-85e1-003f0c95895a
-- title:
--   LevyStochCalc source proof: MathFin.integral_mul_compensated_eq_zero
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000

open private regionSigma_le from Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000
/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated-Poisson isometry kernel (increment-independence cornerstone)

The jump analogue of `Foundations/ItoIsometryAdapted.lean`. For a Poisson random measure `N`,
the second-moment energy identities that the Itô–Lévy isometry sums are:

* diagonal `𝔼[φ² · Ñ(box)²] = 𝔼[φ²] · ν̂(box)` (`integral_adapted_sq_mul_compensated_sq`);
* cross `𝔼[φ · Ñ(box₁) · ψ · Ñ(box₂)] = 0` for disjoint boxes with `box₁` in the past-region
  of `box₂` (`integral_cross_compensated_eq_zero`).

Both flow from the single structure field `indep_of_disjoint_region` (independent scattering):
`N` on any region disjoint from `D` is independent of `N(·, D)`. The past `σ`-algebra at a time
`s` and the count on any box disjoint from a future box both live in that "disjoint region", so
one field closes every cross-term — the different-time cross pairs *and* the same-time /
different-mark cross pairs that a `time × mark` simple integrand produces.

## Provenance

Design mirrors our continuous `ItoIsometryAdapted`; the PRM object is from
`Foundations/PoissonRandomMeasure` (field shape consulted from `cgarryZA/LevyStochCalc`, cited).
The isometry content is our own — LevyStochCalc states it as cited axiom #6.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The past and disjoint-region `σ`-algebras -/

/-! ### Measurability of adapted integrands and compensated increments -/

/-! ### The independence cornerstone and the energy identities -/


theorem _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d (N : PoissonRandomMeasure P ν) {D : Set (ℝ × E)}
    (hD : MeasurableSet D) (hfin : referenceIntensity ν D ≠ ⊤)
    {X : Ω → ℝ} (hX : Measurable[N.regionSigma D] X) :
    ∫ ω, X ω * N.compensated D ω ∂P = 0 := by
  have hXm : Measurable X := hX.mono (regionSigma_le N D) le_rfl
  have hfield : Indep (N.regionSigma D)
      (MeasurableSpace.comap (fun ω => N.N ω D) inferInstance) P := N.indep_of_disjoint_region hD
  have hraw : IndepFun X (fun ω => N.N ω D) P :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hX))
  have hcomp : IndepFun X (N.compensated D) P := by
    have h := hraw.comp (φ := (id : ℝ → ℝ))
      (ψ := fun x : ℝ≥0∞ => x.toReal - (MathFin.referenceIntensity ν D).toReal) measurable_id (by fun_prop)
    simp only [Function.comp_def, id_eq] at h
    exact h
  rw [hcomp.integral_fun_mul_eq_mul_integral hXm.aestronglyMeasurable
        (N.measurable_compensated hD).aestronglyMeasurable,
      MathFin.compensated_integral_zero N hD hfin, mul_zero]
end MathFin


