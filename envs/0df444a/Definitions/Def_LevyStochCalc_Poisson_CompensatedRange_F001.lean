-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001
-- name    : LevyStochCalc_Poisson_CompensatedRange_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:33.971417+00:00
-- url     : https://prove2.me/theorems/cf0d7a9c-843f-4b5a-adca-6aa2380f6009
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000
import Definitions.Def_SourceProof_5fad5a5e72ace6c4e33f3a33
import Definitions.Def_SourceProof_607da3f21f7f718eec49c956
import Definitions.Def_SourceProof_67a5d0b973066b3e65d99ba2
import Definitions.Def_SourceProof_79a6cde54e31b0f9d920e0b6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- Scalar multiples of progressively measurable marked processes are progressively
measurable. -/
theorem markedProgressivelyMeasurable_const_mul {φ : Ω → ℝ → E → ℝ}
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) (c : ℝ) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => c * φ ω s e :=
  (continuous_const.mul continuous_id).comp_markedProgressivelyMeasurable (mul_zero c) h
end Progressive

/-- A marked integrand admissible for the compensated integral, supported in the horizon
`[0, T]`. -/
structure MarkedHorizonIntegrand (P : Measure Ω) (ν : Measure E)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The underlying marked process. -/
  toFun : Ω → ℝ → E → ℝ
  /-- Joint measurability in the sample point, the time and the mark. -/
  measurable_uncurry : Measurable fun p : Ω × ℝ × E => toFun p.1 p.2.1 p.2.2
  /-- Progressive measurability for the filtration. -/
  progressive : Probability.MarkedProgressivelyMeasurable ℱ toFun
  /-- The process vanishes off the horizon. -/
  vanishing : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → toFun ω s e = 0
  /-- The energy on the horizon is finite. -/
  energy_ne_top : markedEnergy P ν T toFun ≠ ⊤
namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The global square-integrability the compensated integral asks for. -/
theorem sq_int_global (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖G.toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T' _ =>
  lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_5fad5a5e72ace6c4e33f3a33 G.vanishing T')
    (lt_top_iff_ne_top.mpr G.energy_ne_top)
/-- The compensated integral of an admissible marked integrand over the horizon. -/
noncomputable def integral (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (G : MarkedHorizonIntegrand P ν ℱ T) : Ω → ℝ :=
  stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive G.sq_int_global T
/-- The zero integrand. -/
def zero (P : Measure Ω) (ν : Measure E) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun _ _ _ => 0
  measurable_uncurry := measurable_const
  progressive := markedProgressivelyMeasurable_zero ℱ
  vanishing := fun _ _ _ _ => rfl
  energy_ne_top := by simp [markedEnergy]
/-- The sum of two admissible marked integrands. -/
noncomputable def add (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => G₁.toFun ω s e + G₂.toFun ω s e
  measurable_uncurry := G₁.measurable_uncurry.add G₂.measurable_uncurry
  progressive := _root_.Prove2MeSourceProof.h_67a5d0b973066b3e65d99ba2 G₁.progressive G₂.progressive
  vanishing := fun ω s e hs => by rw [G₁.vanishing ω s e hs, G₂.vanishing ω s e hs, add_zero]
  energy_ne_top := markedEnergy_add_ne_top G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.energy_ne_top G₂.energy_ne_top
/-- A scalar multiple of an admissible marked integrand. -/
noncomputable def smul (c : ℝ) (G : MarkedHorizonIntegrand P ν ℱ T) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => c * G.toFun ω s e
  measurable_uncurry := measurable_const.mul G.measurable_uncurry
  progressive := markedProgressivelyMeasurable_const_mul G.progressive c
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_const_mul_ne_top G.measurable_uncurry G.energy_ne_top c
section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integral of an admissible marked integrand is square integrable. -/
theorem memLp (G : MarkedHorizonIntegrand P ν ℱ T) : MemLp (G.integral N hℱ) 2 P :=
  stochasticIntegral_memLp N ℱ hℱ G.toFun G.measurable_uncurry G.progressive G.sq_int_global T
/-- The isometry of differences in terms of the marked energy. -/
theorem lintegral_sq_integral_sub (hT : 0 < T) (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    ∫⁻ ω, (‖G₁.integral N hℱ ω - G₂.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = markedEnergy P ν T fun ω s e => G₁.toFun ω s e - G₂.toFun ω s e :=
  itoIsometry_diff_compensated N ℱ hℱ G₁.toFun G₂.toFun G₁.measurable_uncurry
    G₂.measurable_uncurry G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global T hT
/-- The integral of the zero integrand vanishes. -/
theorem integral_zero (hT : 0 < T) :
    (MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ =ᵐ[P] 0 := by
  have hiso := isometry_stochasticIntegral N ℱ hℱ (MarkedHorizonIntegrand.zero P ν ℱ T).toFun
    (MarkedHorizonIntegrand.zero P ν ℱ T).measurable_uncurry
    (MarkedHorizonIntegrand.zero P ν ℱ T).progressive
    (MarkedHorizonIntegrand.zero P ν ℱ T).sq_int_global T hT
  have h0 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖(MarkedHorizonIntegrand.zero P ν ℱ T).toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) = 0 := by
    simp [MarkedHorizonIntegrand.zero]
  have hzero : ∫⁻ ω,
      (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    hiso.trans h0
  have hae : AEMeasurable
      (fun ω => (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((memLp N hℱ (MarkedHorizonIntegrand.zero P ν ℱ T)).aestronglyMeasurable.aemeasurable
      ).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖(MarkedHorizonIntegrand.zero P ν ℱ T).integral N hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3
/-- Additivity of the integral on admissible marked integrands. -/
theorem integral_add (hT : 0 < T) (G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T) :
    (G₁.add G₂).integral N hℱ =ᵐ[P] fun ω => G₁.integral N hℱ ω + G₂.integral N hℱ ω :=
  _root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 N ℱ hℱ G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global
    (G₁.add G₂).measurable_uncurry (G₁.add G₂).progressive (G₁.add G₂).sq_int_global hT
/-- Homogeneity of the integral on admissible marked integrands. -/
theorem integral_smul (hT : 0 < T) (c : ℝ) (G : MarkedHorizonIntegrand P ν ℱ T) :
    (G.smul c).integral N hℱ =ᵐ[P] fun ω => c * G.integral N hℱ ω :=
  _root_.Prove2MeSourceProof.h_607da3f21f7f718eec49c956 N ℱ hℱ G.measurable_uncurry G.progressive G.sq_int_global c
    (G.smul c).measurable_uncurry (G.smul c).progressive (G.smul c).sq_int_global hT
end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Representation

end LevyStochCalc.Poisson.Compensated


