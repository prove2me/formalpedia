-- Prove2me | Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001
-- name    : MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:33:01.782992+00:00
-- url     : https://prove2.me/theorems/ba3f18e0-f1d8-460a-8339-33ebded31a87
-- title:
--   LevyStochCalc source module: MathFin.Foundations.PoissonCompensatedIsometryAdapted
-- statement:
--   Exact source-faithful declarations from MathFin.Foundations.PoissonCompensatedIsometryAdapted in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000
import Definitions.Def_SourceProof_8e8c6bf1745159f9e5de9b8d

open private comap_le_regionSigma pastSigma_le_regionSigma from Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000
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

/-- **Diagonal energy** (the isometry's diagonal term): for `φ` adapted at `s`,
`𝔼[φ² · Ñ((s,t] × A)²] = 𝔼[φ²] · ν̂((s,t] × A)`. The increment's square is independent of
the past (`adapted_indepFun_compensated`, squared) and has mean `ν̂(box)`
(`compensated_integral_sq`). -/
theorem integral_adapted_sq_mul_compensated_sq (N : PoissonRandomMeasure P ν)
    {s t : ℝ} {A : Set E} (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) :
    ∫ ω, (φ ω) ^ 2 * (N.compensated (Set.Ioc s t ×ˢ A) ω) ^ 2 ∂P
      = (∫ ω, (φ ω) ^ 2 ∂P) * (referenceIntensity ν (Set.Ioc s t ×ˢ A)).toReal := by
  have hbox : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := referenceIntensity_box_ne_top hAfin
  have hφm : Measurable φ := hφ.measurable
  have hÑm : Measurable (N.compensated (Set.Ioc s t ×ˢ A)) := N.measurable_compensated hbox
  have hindep : IndepFun φ (N.compensated (Set.Ioc s t ×ˢ A)) P :=
    adapted_indepFun_compensated N hA hφ
  have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have key := hindep2.integral_fun_mul_eq_mul_integral (hφm.pow_const 2).aestronglyMeasurable
    (hÑm.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  rw [key, compensated_integral_sq N hbox hfin]
/-- **Cross-term vanishing** (both cross families of a `time × mark` simple integrand). For
`φa` adapted at `sa`, `φb` adapted at `sb` with `sa ≤ sb`, a measurable `Ba` disjoint from the
future box `(sb, tb] × Ab`,

  `𝔼[(φa · Ñ(Ba)) · (φb · Ñ((sb,tb] × Ab))] = 0`.

The first factor `φa · Ñ(Ba) · φb` is measurable for `regionSigma((sb,tb] × Ab)` — `φa`, `φb`
past-adapted (their pasts precede the box), `Ñ(Ba)` on a disjoint box — so it pairs to zero
against the fresh increment by `integral_mul_compensated_eq_zero`. Different-time cross pairs
take `Ba = (sa, ta] × Aa` with `ta ≤ sb`; same-time / different-mark pairs take
`Ba = (sb, tb] × Aa` with `Aa ∩ Ab = ∅`. -/
theorem integral_cross_compensated_eq_zero (N : PoissonRandomMeasure P ν)
    {sa sb tb : ℝ} (hab : sa ≤ sb)
    {Ba : Set (ℝ × E)} (hBa : MeasurableSet Ba) {Ab : Set E} (hAb : MeasurableSet Ab)
    (hAbfin : ν Ab ≠ ⊤) (hdisj : Disjoint Ba (Set.Ioc sb tb ×ˢ Ab))
    {φa φb : Ω → ℝ} (hφa : N.AdaptedAt sa φa) (hφb : N.AdaptedAt sb φb) :
    ∫ ω, (φa ω * N.compensated Ba ω)
          * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) ∂P = 0 := by
  have hboxbms : MeasurableSet (Set.Ioc sb tb ×ˢ Ab) := measurableSet_Ioc.prod hAb
  have hfin : referenceIntensity ν (Set.Ioc sb tb ×ˢ Ab) ≠ ⊤ := referenceIntensity_box_ne_top hAbfin
  have hφa' : Measurable[N.pastSigma sa] φa := hφa
  have hφb' : Measurable[N.pastSigma sb] φb := hφb
  have hXa : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)] φa :=
    hφa'.mono (pastSigma_le_regionSigma N hab Ab) le_rfl
  have hXÑa : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)] (N.compensated Ba) := by
    show Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)]
      fun ω => (N.N ω Ba).toReal - (referenceIntensity ν Ba).toReal
    have hc : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)] fun ω => N.N ω Ba :=
      (measurable_iff_comap_le.mpr le_rfl).mono (comap_le_regionSigma N hdisj hBa) le_rfl
    exact hc.ennreal_toReal.sub measurable_const
  have hXb : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)] φb :=
    hφb'.mono (pastSigma_le_regionSigma N le_rfl Ab) le_rfl
  have hX : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)]
      fun ω => φa ω * N.compensated Ba ω * φb ω := (hXa.mul hXÑa).mul hXb
  have hzero := _root_.Prove2MeSourceProof.h_8e8c6bf1745159f9e5de9b8d N hboxbms hfin hX
  rw [← hzero]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
end MathFin


