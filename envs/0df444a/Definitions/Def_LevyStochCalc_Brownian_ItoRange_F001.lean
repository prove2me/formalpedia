-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
-- name    : LevyStochCalc_Brownian_ItoRange_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:48:11.540641+00:00
-- url     : https://prove2.me/theorems/c6095ee8-b41f-465b-a8c6-88dcd1ff5314
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {T : ℝ}

end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integrals of admissible integrands, as a submodule of `L²`. -/
noncomputable def itoRange (hT : 0 < T) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {u : Lp ℝ 2 P | ∃ G : HorizonIntegrand P ℱ T, (u : Ω → ℝ) =ᵐ[P] G.integral W hℱ}
  zero_mem' := by
    refine ⟨HorizonIntegrand.zero P ℱ T, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P, HorizonIntegrand.integral_zero W hℱ hT] with ω h1 h2
    rw [h1, h2]
  add_mem' := by
    intro u v hu hv
    obtain ⟨G₁, h₁⟩ := hu
    obtain ⟨G₂, h₂⟩ := hv
    refine ⟨G₁.add G₂, ?_⟩
    filter_upwards [Lp.coeFn_add u v, h₁, h₂, HorizonIntegrand.integral_add W hℱ hT G₁ G₂]
      with ω e1 e2 e3 e4
    rw [e1, Pi.add_apply, e2, e3, e4]
  smul_mem' := by
    intro c u hu
    obtain ⟨G, h⟩ := hu
    refine ⟨G.smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, h, HorizonIntegrand.integral_smul W hℱ hT c G]
      with ω e1 e2 e3
    rw [e1, Pi.smul_apply, e2, e3, smul_eq_mul]
/-- The `L²`-distance between two Itô integrals is the energy of the difference. -/
theorem energy_eq_edist_sq (hT : 0 < T) {u v : Lp ℝ 2 P} {G₁ G₂ : HorizonIntegrand P ℱ T}
    (h₁ : (u : Ω → ℝ) =ᵐ[P] G₁.integral W hℱ) (h₂ : (v : Ω → ℝ) =ᵐ[P] G₂.integral W hℱ) :
    energy P T (fun ω s => G₁.toFun ω s - G₂.toFun ω s) = edist u v ^ 2 := by
  rw [Lp.edist_def, eLpNorm_sq_eq_lintegral,
    ← HorizonIntegrand.lintegral_sq_integral_sub W hℱ hT G₁ G₂]
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, h₂] with ω e1 e2
  simp only [Pi.sub_apply]
  rw [e1, e2]
end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Representation

end LevyStochCalc.Brownian.Ito


