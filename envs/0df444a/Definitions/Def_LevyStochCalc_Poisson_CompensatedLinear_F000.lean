-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F000
-- name    : LevyStochCalc_Poisson_CompensatedLinear_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:08:43.688242+00:00
-- url     : https://prove2.me/theorems/9d046bcd-a400-4ac9-b0ae-7a510831fc65
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedLinear
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedLinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Poisson_Compensated_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The marked energy density of an integrand at a sample point. -/
noncomputable def markedDensity (ν : Measure E) (T : ℝ) (φ : Ω → ℝ → E → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
omit [IsProbabilityMeasure P] in
theorem measurable_markedDensity {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    Measurable (markedDensity (Ω := Ω) ν T φ) := by
  have hsq : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  have hmid : Measurable fun q : (Ω × ℝ) × E => (‖φ q.1.1 q.1.2 q.2‖₊ : ℝ≥0∞) ^ 2 :=
    hsq.comp (by fun_prop : Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))
  exact (hmid.lintegral_prod_right' (ν := ν)).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))
/-- The squared extended norm of the mark integral, at a fixed sample point and time. -/
theorem measurable_markSlice {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (ω : Ω) :
    Measurable fun s : ℝ => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  have hsq : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  have hslice : Measurable fun q : ℝ × E => (‖φ ω q.1 q.2‖₊ : ℝ≥0∞) ^ 2 :=
    hsq.comp (measurable_prodMk_left (x := ω))
  exact hslice.lintegral_prod_right' (ν := ν)
section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

end Linearity

end LevyStochCalc.Poisson.Compensated


