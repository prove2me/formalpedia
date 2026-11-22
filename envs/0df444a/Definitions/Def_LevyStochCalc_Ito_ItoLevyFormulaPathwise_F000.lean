-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaPathwise_F000
-- name    : LevyStochCalc_Ito_ItoLevyFormulaPathwise_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T14:12:28.94319+00:00
-- url     : https://prove2.me/theorems/29d303b0-e75f-4aae-8c34-55114e242bae
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.ItoLevyFormulaPathwise
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.ItoLevyFormulaPathwise in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedNonpos_F000
import Definitions.Def_SourceProof_066bb78ae9c9fe13ff9f9ec5
import Definitions.Def_SourceProof_6293e0a2c6bb1095b807c809

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at every time along one path

The Itô–Lévy formula `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` holds, for each
horizon separately, off a null set depending on that horizon. Both sides of the identity are
right-continuous in the horizon along almost every path, so the union of the null sets over the
rational horizons is again null and the identity holds at every horizon `T ≥ 0` simultaneously
off a single null set.

The compensated-Poisson leg is càdlàg at every sample point by construction. The Brownian leg
`LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral` is defined one time
at a time, as an equivalence class for each horizon, and so carries no path regularity; the first
statement below therefore takes a process `M` that is a version of it and is right-continuous
along every path, and the second supplies such a version from
`LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general_pathwise` — the four-term formula at
  every horizon off one null set, for a prescribed right-continuous version of the Brownian leg.
* `LevyStochCalc.Ito.JumpFormula.exists_itoLevyFormula_general_pathwise` — the same, for a
  version of the Brownian leg that is adapted to the right-continuous filtration, jointly
  measurable, càdlàg at every sample point and a martingale.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian.Multidim

universe u v

section Pathwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- **The Itô–Lévy formula for a jump diffusion, at every horizon along one path, with a
canonical Brownian leg.** Under the hypotheses of `itoLevyFormula_general_pathwise` other than
those on the Brownian leg, the Brownian leg has a version that is adapted to the right-continuous
filtration, jointly measurable in the time and the sample point, càdlàg at every sample point and
a martingale, and for it the four-term identity holds at every horizon `T ≥ 0` simultaneously,
off a single null set. -/
theorem exists_itoLevyFormula_general_pathwise (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ T' : ℝ, 0 < T' → ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤)
    (h_drift_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => driftIntegrand u coeffs s (X.X s ω)) (Set.Icc (0 : ℝ) b) volume)
    (h_cd_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => ∫ e, compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)
        (Set.Icc (0 : ℝ) b) volume) :
    ∃ M : ℝ → Ω → ℝ, Adapted S.ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P]
        MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
          (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
          (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
          (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
          h_sigmaGrad_sq t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))
        ∧ ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M S.ℱ.rightCont P ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
        u T (X.X T ω) - u 0 (X.X 0 ω)
          = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
            + M T ω
            + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
                (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
                (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
                (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
                h_jumpInt_sq T ω
            + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
                compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  have hrc : S.ℱ.rightCont = S.ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    rw [hrc]
    exact hℱ0 t ht
  obtain ⟨M, hMadapt, hMmeas, hMae, hMcad, hMmart⟩ :=
    _root_.Prove2MeSourceProof.h_6293e0a2c6bb1095b807c809 W S.ℱ S.isBrownian
      (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
      (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
      (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
      h_sigmaGrad_sq hℱ0' hnull
  exact ⟨M, hMadapt, hMmeas, hMae, hMcad, hMmart,
    _root_.Prove2MeSourceProof.h_066bb78ae9c9fe13ff9f9ec5 W N coeffs x₀ X S hℱ0 hnull hμmeas hσmeas hγmeas hμq u hu
      h_sigmaGrad_sq h_jumpInt_sq h_compDrift_int h_drift_loc h_cd_loc M hMae
      fun ω t => (hMcad ω t).1⟩
end Pathwise

end LevyStochCalc.Ito.JumpFormula


