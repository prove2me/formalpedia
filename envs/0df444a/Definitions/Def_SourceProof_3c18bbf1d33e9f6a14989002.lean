-- Prove2me | Definitions.Def_SourceProof_3c18bbf1d33e9f6a14989002
-- name    : SourceProof_3c18bbf1d33e9f6a14989002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:44:33.951389+00:00
-- url     : https://prove2.me/theorems/55e24fc2-0958-442b-bb73-6f4aa5fb29e2
-- title:
--   LevyStochCalc source module: SourceProof_3c18bbf1d33e9f6a14989002
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_SdeDataOfSolvesOn_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the derived integrands along a path

The two stochastic integrals of the Itô–Lévy formula at bounded derivatives carry the integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` evaluated along a path. For a `C²` state function with bounded
gradient and coefficients that are regular and Lipschitz, each of these is jointly measurable,
progressively measurable in the sense its integral asks for, and of finite energy on every
window; along the path the drift is integrable and the compensator-drift integrand has finite
mark energy, almost surely.
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

theorem _root_.Prove2MeSourceProof.h_3c18bbf1d33e9f6a14989002 (hu : ContDiff ℝ 2 (Function.uncurry u))
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
  · exact (LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry hu i).measurable.comp hstate
end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula


