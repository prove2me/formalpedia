-- Prove2me | Definitions.Def_SourceProof_7b7fe4c6b4bf6f12571973df
-- name    : SourceProof_7b7fe4c6b4bf6f12571973df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:08:29.337247+00:00
-- url     : https://prove2.me/theorems/a1daaeef-71ad-439e-9ee8-091416c43ee8
-- title:
--   LevyStochCalc source module: SourceProof_7b7fe4c6b4bf6f12571973df
-- statement:
--   The original source theorem `LevyStochCalc.Probability.measurable_of_ae_eq_of_null_sets` comes from the `LevyStochCalc.Ito.JumpDiffusionAdapted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Adaptedness of a jump diffusion

The jump-diffusion integral equation of `LevyStochCalc.Ito.Picard.SolvesOn` expresses the path
map at time `t` as the sum of a drift integral over `[0, t]`, a Brownian Itô integral and a
compensated Poisson integral. The Brownian integral is strongly adapted to `ℱ`
(`LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted`), the compensated
integral is adapted to the right-continuation `ℱ₊` of `ℱ`
(`LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted`), and the drift integral of a
progressively measurable integrand is `ℱ t`-measurable
(`ProgressivelyMeasurable.measurable_setIntegral_Icc`), so the right-hand side is
`ℱ₊ t`-measurable and the equation transfers that measurability to the path map up to a null
set.

## Main statements

* `SolvesOn.aeStronglyMeasurable_rightCont` — the path map at time `t` is
  `ℱ₊ t`-a.e.-strongly measurable, given progressive measurability of the drift
  integrand along the path.
* `SolvesOn.stronglyMeasurable_rightCont` — the same with the null set absorbed, when `ℱ 0`
  contains the `P`-null sets and the path map is jointly measurable.
* `SolvesOn.stronglyMeasurable_of_isRegular` — under the usual conditions and the Lipschitz and
  regularity hypotheses on the coefficients, every jointly measurable, `S²`-bounded solution on
  all horizons is `ℱ t`-strongly measurable at every `t ≥ 0`; no hypothesis on the drift
  integrand is needed.
* `JumpDiffusion.stronglyMeasurable_of_solvesOn`, `JumpDiffusion.exists_unique_adapted` — the
  same for a `JumpDiffusion` solving the equation relative to `ℱ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {α : Type*} [MeasurableSpace α]


theorem _root_.Prove2MeSourceProof.h_7b7fe4c6b4bf6f12571973df {m₀ m : MeasurableSpace Ω} {P : @Measure Ω m₀}
    {f g : Ω → α} (hnull : ∀ s : Set Ω, MeasurableSet[m₀] s → P s = 0 → MeasurableSet[m] s)
    (hf : Measurable[m₀] f) (hg : Measurable[m] g) (hfg : f =ᵐ[P] g) :
    Measurable[m] f := by
  letI : MeasurableSpace Ω := m₀
  obtain ⟨A, hsub, hAmeas, hAzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (μ := P) (MeasureTheory.ae_iff.mp hfg)
  intro s hs
  have hsplit : f ⁻¹' s = (f ⁻¹' s ∩ Aᶜ) ∪ (f ⁻¹' s ∩ A) := by
    rw [← Set.inter_union_distrib_left, Set.compl_union_self, Set.inter_univ]
  have hleft : f ⁻¹' s ∩ Aᶜ = g ⁻¹' s ∩ Aᶜ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    refine and_congr_left fun hωA => ?_
    have hω : f ω = g ω := by
      by_contra hne
      exact hωA (hsub hne)
    rw [hω]
  have hAm : MeasurableSet[m] A := hnull A hAmeas hAzero
  rw [hsplit, hleft]
  refine MeasurableSet.union ((hg hs).inter hAm.compl) (hnull _ ((hf hs).inter hAmeas) ?_)
  exact measure_mono_null Set.inter_subset_right hAzero
end LevyStochCalc.Probability

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

end LevyStochCalc.Ito.Picard

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
variable {ν : Measure E} [SigmaFinite ν]

end JumpDiffusion
end LevyStochCalc.Ito.Setting


