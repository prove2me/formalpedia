-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellPairing_F001
-- name    : LevyStochCalc_Driver_CellPairing_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:57:42.49702+00:00
-- url     : https://prove2.me/theorems/e9fb60ed-dd17-4f5b-8775-5889ed193449
-- title:
--   LevyStochCalc source module: LevyStochCalc.Driver.CellPairing
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Driver.CellPairing in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F001
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002
import Definitions.Def_LevyStochCalc_Poisson_CellIntegrand_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002
import Definitions.Def_SourceProof_8947220630d6423d404c65c5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱW in
/-- **The `dW` term pairs to zero.** A real weight orthogonal to every Itô integral, times a
bounded weight measurable before the window, is orthogonal to the Itô integral of any bounded
progressive integrand supported in the window. -/
theorem integral_mul_stochasticIntegralBrownian_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZp : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    {V : Ω → ℝ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    (hVa : StronglyMeasurable[ℱ a] V)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ}
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω ∂P = 0 := by
  have hZc : MemLp (fun ω => ((Z ω : ℝ) : ℂ)) 2 P := memLp_ofReal hZ2
  have hVc : Measurable fun ω => ((V ω : ℝ) : ℂ) := Complex.measurable_ofReal.comp hVm
  have hVcb : ∀ ω, ‖((V ω : ℝ) : ℂ)‖ ≤ Mv := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hVb ω
  have hVca : StronglyMeasurable[ℱ a] fun ω => ((V ω : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hVa
  have hc := _root_.Prove2MeSourceProof.h_8947220630d6423d404c65c5 ha hab hZc hZp hVc hMv0 hVcb hVca hKm hKp hKbd hmg hpg
    hqg ht
  set f : Ω → ℝ := fun ω => Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
    (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω with hf
  have hcast : ∀ ω : Ω, ((Z ω : ℝ) : ℂ) * ((V ω : ℝ) : ℂ) * ((stochasticIntegralBrownian W ℱ hℱW
        (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
      = ((f ω : ℝ) : ℂ) := by
    intro ω
    rw [hf]
    push_cast
    ring
  simp_rw [hcast] at hc
  have hre : ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) := integral_ofReal
  rw [hre] at hc
  exact_mod_cast hc
end BrownianTerm

section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end Assembly

end LevyStochCalc.Driver


