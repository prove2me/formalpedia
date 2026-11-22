-- Prove2me | Definitions.Def_SourceProof_066bb78ae9c9fe13ff9f9ec5
-- name    : SourceProof_066bb78ae9c9fe13ff9f9ec5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T14:07:41.275822+00:00
-- url     : https://prove2.me/theorems/cbd8e8c8-298a-4eaa-bf15-321af377a8a2
-- title:
--   LevyStochCalc source module: SourceProof_066bb78ae9c9fe13ff9f9ec5
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general_pathwise` comes from the `LevyStochCalc.Ito.ItoLevyFormulaPathwise` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedNonpos_F000
import Definitions.Def_SourceProof_fc92219c61092a0b1afac4f9

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


theorem _root_.Prove2MeSourceProof.h_066bb78ae9c9fe13ff9f9ec5 (x₀ : Fin n → ℝ)
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
        (Set.Icc (0 : ℝ) b) volume)
    (M : ℝ → Ω → ℝ)
    (hMae : ∀ t : ℝ, M t =ᵐ[P]
      MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
        (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
        (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
        (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
        h_sigmaGrad_sq t)
    (hMright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
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
  set J : ℝ → Ω → ℝ := LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
      (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas X.measurable_path)
      (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
      h_jumpInt_sq with hJ
  have hJcad := LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N S.ℱ S.isPoisson
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
      (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas X.measurable_path)
      (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
      h_jumpInt_sq
  refine _root_.Prove2MeSourceProof.h_231d4b01442d4e78331883f1 (P := P)
    (Y := fun T ω => u T (X.X T ω) - u 0 (X.X 0 ω))
    (Z := fun T ω => (∫ s in Set.Icc (0 : ℝ) T, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs s (X.X s ω))
      + M T ω + J T ω
      + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν) ?_ ?_ ?_
  · -- the identity at the rational horizons
    intro q hq
    rcases eq_or_lt_of_le hq with heq | hpos
    · -- the horizon `0`, where both stochastic legs vanish
      have hzeroM : M (q : ℝ) =ᵐ[P] 0 := (hMae _).trans
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W S.ℱ S.isBrownian _ _ _ _
          (le_of_eq heq.symm))
      have hzeroJ : J (q : ℝ) =ᵐ[P] 0 :=
        (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N S.ℱ S.isPoisson
            _ _ _ h_jumpInt_sq _).trans
          (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N S.ℱ S.isPoisson
            _ _ _ h_jumpInt_sq (le_of_eq heq.symm))
      filter_upwards [hzeroM, hzeroJ] with ω hM0 hJ0
      rw [← heq] at hM0 hJ0
      simp only [← heq, Set.Icc_self]
      simp [hM0, hJ0]
    · filter_upwards [_root_.Prove2MeSourceProof.h_fc92219c61092a0b1afac4f9 W N coeffs x₀ X S hℱ0 hnull hμmeas hσmeas hγmeas
        hμq u hu (q : ℝ) hpos h_sigmaGrad_sq h_jumpInt_sq (h_compDrift_int (q : ℝ) hpos),
        hMae (q : ℝ)] with ω hω hMω
      rw [hMω]
      exact hω
  · -- right-continuity of the left side in the horizon
    filter_upwards [X.cadlag_paths] with ω hω t ht
    have hpair : Tendsto (fun s => ((s, X.X s ω) : ℝ × (Fin n → ℝ))) (𝓝[>] t)
        (𝓝 ((t, X.X t ω) : ℝ × (Fin n → ℝ))) :=
      ((continuous_id.tendsto t).mono_left nhdsWithin_le_nhds).prodMk_nhds (hω t ht).1
    exact ((hu.continuous.tendsto _).comp hpair).sub_const _
  · -- right-continuity of the right side in the horizon
    filter_upwards [h_drift_loc, h_cd_loc, hJcad] with ω hd hc hJω t ht
    have h1 : Tendsto (fun s => ∫ r in Set.Icc (0 : ℝ) s, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs r (X.X r ω))
        (𝓝[>] t) (𝓝 (∫ r in Set.Icc (0 : ℝ) t, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs r (X.X r ω))) :=
      ((_root_.Prove2MeSourceProof.h_1f982f95c243b7704e920390
        hd).tendsto t).mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun s => ∫ r in Set.Icc (0 : ℝ) s,
          ∫ e, LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ r (X.X r ω) e ∂ν)
        (𝓝[>] t) (𝓝 (∫ r in Set.Icc (0 : ℝ) t,
          ∫ e, LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ r (X.X r ω) e ∂ν)) :=
      ((_root_.Prove2MeSourceProof.h_1f982f95c243b7704e920390
        hc).tendsto t).mono_left nhdsWithin_le_nhds
    exact ((h1.add (hMright ω t)).add (hJω t).1).add h4
end Pathwise

end LevyStochCalc.Ito.JumpFormula


