-- Prove2me | Definitions.Def_SourceProof_1c3b8c92624b77e806423413
-- name    : SourceProof_1c3b8c92624b77e806423413
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:32:35.316205+00:00
-- url     : https://prove2.me/theorems/6c2e9b31-b080-4d3a-9029-f8b46e3410f2
-- title:
--   LevyStochCalc source proof: MathFin.memLp_adapted_mul_compensated
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000
import Definitions.Def_SourceProof_09a1d2ad90db017031836da3

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


theorem _root_.Prove2MeSourceProof.h_1c3b8c92624b77e806423413 (N : PoissonRandomMeasure P ν) {s t : ℝ}
    {A : Set E} (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφL2 : MemLp φ 2 P) :
    MemLp (fun ω => φ ω * N.compensated (Set.Ioc s t ×ˢ A) ω) 2 P := by
  have hbox : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : MathFin.referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := MathFin.referenceIntensity_box_ne_top hAfin
  have hφm : Measurable φ := hφ.measurable
  have hÑm : Measurable (N.compensated (Set.Ioc s t ×ˢ A)) := N.measurable_compensated hbox
  have hindep : IndepFun φ (N.compensated (Set.Ioc s t ×ˢ A)) P :=
    MathFin.adapted_indepFun_compensated N hA hφ
  have hφsq : Integrable (fun ω => (φ ω) ^ 2) P := hφL2.integrable_sq
  have hÑsq : Integrable (fun ω => (N.compensated (Set.Ioc s t ×ˢ A) ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hbox hfin).integrable_sq
  have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have hprod : Integrable
      (fun ω => (φ ω) ^ 2 * (N.compensated (Set.Ioc s t ×ˢ A) ω) ^ 2) P :=
    hindep2.integrable_mul hφsq hÑsq
  refine (memLp_two_iff_integrable_sq (hφm.mul hÑm).aestronglyMeasurable).mpr ?_
  simpa [mul_pow] using hprod
end MathFin


