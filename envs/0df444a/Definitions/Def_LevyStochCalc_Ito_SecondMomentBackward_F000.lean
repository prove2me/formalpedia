-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentBackward_F000
-- name    : LevyStochCalc_Ito_SecondMomentBackward_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:36:15.531754+00:00
-- url     : https://prove2.me/theorems/57189def-42c0-4818-9770-ae76bcc15f47
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentBackward
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentBackward. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F002
import Definitions.Def_SourceProof_126f404b8a8da5b36bfb989a
import Definitions.Def_SourceProof_d8b446e22164b7620e52d72e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The backward weighted energy inequality

For an Itô–Lévy process `X` over a Lévy driver that vanishes at a horizon `T`, the exponentially
weighted second moment identity

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`

has vanishing left-hand side and a nonnegative initial term, so the weighted energy of the
process and of its two integrands is dominated by the weighted pairing of the process against
the negated drift,

`∫_0^T e^{βs} (β 𝔼[X_s²] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)) ds
  ≤ ∫_0^T e^{βs} · 2 𝔼[X_s (-b_s)] ds`,

the backward form in which the a-priori estimates for BSDEs with jumps read the quadratic Itô
formula.

## Main statements

* `weighted_energy_le_of_terminal_zero` — the inequality, with the drift negated inside the
  pairing on the right.
* `weighted_energy_le_of_terminal_zero'` — the same with the drift left as it stands and the
  sign carried outside the time integral.
* `integrableOn_integral_mul_self` — the second moment of an Itô–Lévy process is integrable in
  time on every window.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Prelim

/-- A function that on `(0, T]` is a constant plus the primitive of a function integrable on
`[0, T]` is itself integrable on `[0, T]`. -/
theorem integrableOn_of_eq_add_setIntegral {m g : ℝ → ℝ} {m₀ T : ℝ}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (hm : ∀ s ∈ Set.Ioc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r) :
    IntegrableOn m (Set.Icc (0 : ℝ) T) := by
  have hG : ContinuousOn (fun s => m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r) (Set.Icc (0 : ℝ) T) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc hg)
  refine (hG.integrableOn_Icc (μ := volume)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hs0
  exact (hm s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩).symm
/-- An exponential weight preserves integrability on a window. -/
theorem integrableOn_exp_mul {f : ℝ → ℝ} {T : ℝ} (β : ℝ)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    IntegrableOn (fun s => Real.exp (β * s) * f s) (Set.Icc (0 : ℝ) T) :=
  IntegrableOn.continuousOn_mul
    (by fun_prop : Continuous fun s : ℝ => Real.exp (β * s)).continuousOn hf isCompact_Icc
end Prelim

section Backward

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The second moment of an Itô–Lévy process is integrable in time on every window. -/
theorem integrableOn_integral_mul_self
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, X s ω * X s ω ∂P) (Set.Icc (0 : ℝ) T) := by
  refine integrableOn_of_eq_add_setIntegral ?_
    (fun s hs => _root_.Prove2MeSourceProof.h_126f404b8a8da5b36bfb989a h 𝒲 hX₀ hX₀2 hbm hbp hbq hs.1)
  exact (((_root_.Prove2MeSourceProof.h_d8b446e22164b7620e52d72e h hX₀2 hbm hbp hbq hT).const_mul 2).add
    (integrable_finsetSum _ fun j _ =>
      integrableOn_toReal_lintegral (measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT))).add
    (integrableOn_toReal_lintegral (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq T hT))
end Backward

end LevyStochCalc.Ito.SecondMoment


