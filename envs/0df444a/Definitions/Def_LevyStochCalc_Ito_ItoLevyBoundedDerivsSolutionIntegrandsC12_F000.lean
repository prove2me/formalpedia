-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrandsC12_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrandsC12_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:49:42.680461+00:00
-- url     : https://prove2.me/theorems/f3a6fd82-c6e9-40b1-90d5-211241d4e27c
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrandsC12
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrandsC12. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C^{1,2}` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_diffusionIntegrand_path_c12 (hu : IsC12 u)
    (hσ : Measurable (Function.uncurry coeffs.σ)) (hXm : Measurable (Function.uncurry X))
    (j : Fin d) :
    Measurable (Function.uncurry fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j) := by
  have hstate : Measurable fun p : Ω × ℝ => ((p.2, X p.2 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst))
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (X p.2 p.1) i * coeffs.σ p.2 (X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (hu.continuous_gradient i).measurable.comp hstate
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)).comp hstate
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C^{1,2}` state function along a progressively
measurable path is progressively measurable. -/
theorem progressivelyMeasurable_diffusionIntegrand_path_c12
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : IsC12 u) (hσ : Measurable (Function.uncurry coeffs.σ))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (j : Fin d) :
    ProgressivelyMeasurable ℱ fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j := by
  refine progressivelyMeasurable_comp_state hXa
    (f := fun s x => diffusionIntegrand u coeffs.σ s x j) ?_
  change Measurable fun q : ℝ × (Fin n → ℝ) => ∑ i, gradient u q.1 q.2 i * coeffs.σ q.1 q.2 i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (hu.continuous_gradient i).measurable
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_jumpIncrement_path_c12 (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      (fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω')) p.1 p.2.1 p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub
    (hu'.comp (measurable_snd.fst.prodMk hXp))
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function along a progressively
measurable path is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrement_path_c12
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) :
    MarkedProgressivelyMeasurable ℱ
      fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω') := by
  refine _root_.Prove2MeSourceProof.h_ac85444679aa3a412d1927d4 hXa
    (g := fun s x e => u s (x + coeffs.γ s x e) - u s x) ?_
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_fst.prodMk (measurable_snd.fst.add hγ))).sub
    (hu'.comp (measurable_fst.prodMk measurable_snd.fst))
omit [IsProbabilityMeasure P] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function with a bounded gradient has
finite energy on every window on which the jump coefficient along the path has. -/
theorem lintegral_sq_jumpIncrement_path_lt_top_c12 (hu : IsC12 u) {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖u s (X s ω + coeffs.γ s (X s ω) e) - u s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  refine _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909 (a := fun i ω s e => coeffs.γ s (X s ω) e i)
    (c := n * max K₁ 0) (fun i => hγm i) (fun ω s e => ?_) T' (fun i => hγq i T' hT')
  exact abs_mixedJumpIncrement_le_c12 hu hK₁' (le_max_right _ _) s (X s ω) (X s ω) e
end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula


