-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
-- name    : LevyStochCalc_Ito_SecondMomentQuadratic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:28:20.475326+00:00
-- url     : https://prove2.me/theorems/4c7e54c8-e8ec-40d3-ba18-61ada5625da6
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentQuadratic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentQuadratic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in
/-- The energy of a marked integrand on a window, as a lintegral for the product measure. -/
theorem lintegral_prod_marked {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ p, (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
        ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hmeas : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hm.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lintegral_prod _ (hmeas.comp (measurable_prodMk_left (x := ω))).aemeasurable
omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite energy on a window is square integrable for the product
measure. -/
theorem memLp_two_prod_marked {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm.aestronglyMeasurable ?_
  rw [lintegral_prod_marked hm T]
  exact hq
omit [IsProbabilityMeasure P] in
/-- The energy of a marked integrand on a window is the integral of its square for the product
measure. -/
theorem toReal_lintegral_sq_marked_eq {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal
      = ∫ p, φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
  rw [← lintegral_prod_marked hm T, ← integral_mul_self_eq_toReal (memLp_two_prod_marked hm hq)]
/-- A Bochner integral for the product measure of a marked window, iterated. -/
theorem integral_prod_marked {F : Ω × ℝ × E → ℝ} {T : ℝ}
    (hF : Integrable F (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))) :
    ∫ p, F p ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, F (ω, (s, e)) ∂ν ∂volume ∂P := by
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae] with ω hω
  exact integral_prod _ hω
end PolarisedMarked

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Augmented

end LevyStochCalc.Ito.SecondMoment


