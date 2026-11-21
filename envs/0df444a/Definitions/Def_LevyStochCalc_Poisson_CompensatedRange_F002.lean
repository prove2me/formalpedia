-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
-- name    : LevyStochCalc_Poisson_CompensatedRange_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:56.866325+00:00
-- url     : https://prove2.me/theorems/200be0ad-ce5e-4221-9f69-42fb0f854267
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001

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

end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integrals of admissible marked integrands, as a submodule of `L²`. -/
noncomputable def compensatedRange (hT : 0 < T) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {u : Lp ℝ 2 P |
    ∃ G : MarkedHorizonIntegrand P ν ℱ T, (u : Ω → ℝ) =ᵐ[P] G.integral N hℱ}
  zero_mem' := by
    refine ⟨MarkedHorizonIntegrand.zero P ν ℱ T, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P, MarkedHorizonIntegrand.integral_zero N hℱ hT]
      with ω h1 h2
    rw [h1, h2]
  add_mem' := by
    intro u v hu hv
    obtain ⟨G₁, h₁⟩ := hu
    obtain ⟨G₂, h₂⟩ := hv
    refine ⟨G₁.add G₂, ?_⟩
    filter_upwards [Lp.coeFn_add u v, h₁, h₂,
      MarkedHorizonIntegrand.integral_add N hℱ hT G₁ G₂] with ω e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, e3, e4]
  smul_mem' := by
    intro c u hu
    obtain ⟨G, h⟩ := hu
    refine ⟨G.smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, h, MarkedHorizonIntegrand.integral_smul N hℱ hT c G]
      with ω e1 e2 e3
    rw [e1, Pi.smul_apply, e2, e3, smul_eq_mul]
/-- The `L²`-distance between two compensated integrals is the energy of the difference. -/
theorem markedEnergy_eq_edist_sq (hT : 0 < T) {u v : Lp ℝ 2 P}
    {G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T}
    (h₁ : (u : Ω → ℝ) =ᵐ[P] G₁.integral N hℱ) (h₂ : (v : Ω → ℝ) =ᵐ[P] G₂.integral N hℱ) :
    markedEnergy P ν T (fun ω s e => G₁.toFun ω s e - G₂.toFun ω s e) = edist u v ^ 2 := by
  rw [Lp.edist_def, LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral,
    ← MarkedHorizonIntegrand.lintegral_sq_integral_sub N hℱ hT G₁ G₂]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, h₂] with ω e1 e2
  simp only [Pi.sub_apply]
  rw [e1, e2]
end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Representation

end LevyStochCalc.Poisson.Compensated


