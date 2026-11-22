-- Prove2me | Definitions.Def_SourceProof_9c3d4cc8c9faeace6fe19b19
-- name    : SourceProof_9c3d4cc8c9faeace6fe19b19
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:54:58.147782+00:00
-- url     : https://prove2.me/theorems/cc4dd331-6188-4e6f-a64c-b9f2e04e8b83
-- title:
--   LevyStochCalc source module: SourceProof_9c3d4cc8c9faeace6fe19b19
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrandsC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the derived integrands of a `C^{1,2}` state function along a path

The two stochastic integrals of the Itô–Lévy formula carry the integrands `(∇u)ᵀσ` and
`u(x + γ) − u(x)` evaluated along a path. For a state function of class `C^{1,2}` with bounded
gradient and jointly measurable coefficients, each of these is jointly measurable, progressively
measurable in the sense its integral asks for, and of finite energy on every window on which the
coefficient along the path has; the compensator-drift integrand is jointly measurable and, for a
bounded Hessian, has finite mark energy on a window, almost surely.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12` — the
  admissibility of `(∇u)ᵀσ` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top_c12` — the admissibility
  of `u(x + γ) − u(x)` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12` — the
  measurability and the mark integrability of the compensator-drift integrand along the path.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section DerivedIntegrands

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {coeffs : JumpDiffusionCoeffs n d E} {u : ℝ → (Fin n → ℝ) → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_9c3d4cc8c9faeace6fe19b19 (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  have hstate : Measurable fun p : Ω × ℝ × E => ((p.2.1, X p.2.1 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.fst.prodMk hXp
  change Measurable fun p : Ω × ℝ × E =>
    u p.2.1 (X p.2.1 p.1 + coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2) - u p.2.1 (X p.2.1 p.1)
      - ∑ i, coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i * LevyStochCalc.Ito.JumpFormula.gradient u p.2.1 (X p.2.1 p.1) i
  refine ((hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub (hu'.comp hstate)).sub
    (Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply i).comp hγp
  · exact (hu.continuous_gradient i).measurable.comp hstate
end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula


