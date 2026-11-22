-- Prove2me | Definitions.Def_SourceProof_174af6dda35eb2cddfa4078b
-- name    : SourceProof_174af6dda35eb2cddfa4078b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:02:49.291883+00:00
-- url     : https://prove2.me/theorems/51d40319-dfbb-4dd9-a984-1748611d470b
-- title:
--   LevyStochCalc source module: SourceProof_174af6dda35eb2cddfa4078b
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000
import Definitions.Def_SourceProof_225f75f07ee472595cebf470
import Definitions.Def_SourceProof_480386ee1a4adafe3cb7c0b7
import Definitions.Def_SourceProof_55ca53eaccae9591a8954d60
import Definitions.Def_SourceProof_68143de6ea16052afb9e9c57
import Definitions.Def_SourceProof_d628dfa7650ec50fbda91fa8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a `C^{1,2}` state function with bounded derivatives

The Itô–Lévy identity along a jump diffusion for a state function that is once continuously
differentiable in time and twice continuously differentiable in state, with bounded time
derivative, gradient and Hessian, the class `C^{1,2}` being strictly larger than the class of
functions that are `C²` jointly in time and state. The identity for a jointly `C²` state
function is carried to it by joint mollification: the mollifications of a `C^{1,2}` function are
`C²` jointly in time and state and obey the same three bounds, so the identity holds for each of
them, and every term converges as the outer radii of the bumps tend to `0` — the endpoints and
the two Lebesgue integrals pointwise and by dominated convergence, the Brownian and compensated
integrals in `L²`, hence almost surely along a subsequence along which the identity passes to the
limit.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12` — the
  canonical residual is the compensated jump integral plus the compensator-drift integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Main

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

open LevyStochCalc.Ito.IntegralLimit in

theorem _root_.Prove2MeSourceProof.h_174af6dda35eb2cddfa4078b
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    -- Correction 8 (one filtration): the SDE data of `X`, with the usual-conditions shape at
    -- time zero that the truncated paths need.
    (S : LevyStochCalc.Ito.BigJump.SdeData X)
    -- Correction 8 (usual conditions): the filtration of the SDE data is right continuous, so
    -- its right continuation is itself and the two shapes of `hℱ0` are the same statement.
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    -- (3) The structure calls its solution adapted but carries no such field.
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    -- (3') Statement change: `cadlag_paths` holds almost surely and only on `[0, ∞)`, while the
    -- left limits along which the jump coefficient is read must exist at every sample point and
    -- every time for that reading to be a process at all.
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    -- (5) The drift along the path.
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    -- (5') Statement change: `SdeData` carries no drift field, and progressive measurability of
    -- the drift along the path does not follow from its joint measurability.
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- (6) Joint measurability of the jump coefficient.
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : IsC12 u)
    -- The bounded derivatives, coordinatewise.
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    (_h_μ_int : ∀ᵐ ω ∂P, ∀ i : Fin n,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) T))
    (h_sigmaGrad_meas : ∀ j : Fin d,
        Measurable (Function.uncurry
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)))
    (h_sigmaGrad_progMeas : ∀ j : Fin d,
        Probability.ProgressivelyMeasurable S.ℱ
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas :
        Probability.MarkedProgressivelyMeasurable S.ℱ
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (_h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)
        =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- Step 1: a family of bumps whose outer radii tend to `0`, and the mollifications of `u`,
  -- jointly `C²` with the same three bounds.
  obtain ⟨φ, hφ⟩ := LevyStochCalc.Ito.JumpFormula.exists_seq_bump_rOut_tendsto_zero n
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hK₁' : ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₁0 : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hvC : ∀ k, ContDiff ℝ 2 (Function.uncurry (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k))) :=
    fun k => LevyStochCalc.Ito.JumpFormula.contDiff_uncurry_mollifyJoint (N := 2) hu.continuous (φ k)
  have hv0 : ∀ k, ∀ s x, |LevyStochCalc.Ito.JumpFormula.timeDeriv (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x| ≤ K₀ :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_timeDeriv_mollifyJoint_le hu (φ k) hK₀
  have hv1 : ∀ k, ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i| ≤ K₁ :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_gradient_mollifyJoint_le hu (φ k) hK₁
  have hv2 : ∀ k, ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i j| ≤ K₂ :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_hessian_mollifyJoint_le hu (φ k) hK₂
  have hv1' : ∀ k, ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i| ≤ max K₁ 0 :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_gradient_mollifyJoint_le hu (φ k) hK₁'
  -- Step 2: the admissibility of the derived integrands of each mollification, from the bounds
  -- and the SDE data.
  have hBm : ∀ (k : ℕ) (j : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.σ s (X.X s ω) j) :=
    fun k j => LevyStochCalc.Ito.JumpFormula.measurable_uncurry_mixedDiffusionIntegrand S (hvC k) X.X hXm j
  have hBp : ∀ (k : ℕ) (j : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.σ s (X.X s ω) j := by
    intro k j
    change LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s =>
      ∑ i, LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s (X.X s ω) i * coeffs.σ s (X.X s ω) i j
    refine LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_finset_sum _ fun i _ =>
      LevyStochCalc.Probability.ProgressivelyMeasurable.mul ?_ (S.σ_prog i j)
    exact LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state S.X_prog
      (f := fun s x => LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i)
      (LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry (hvC k) i).measurable
  have hBq : ∀ (k : ℕ) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun k j T' hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_diffusionIntegrand_path_lt_top (hv1 k) S.σ_meas S.σ_sq j hT'
  have hCm : ∀ k : ℕ, Measurable (fun p : Ω × ℝ × E =>
      (fun ω' s e => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω' + coeffs.γ s (X.X s ω') e)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω')) p.1 p.2.1 p.2.2) :=
    fun k => LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path (hvC k) hγmeas hXm
  have hCp : ∀ k : ℕ, LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ
      (fun ω' s e => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω' + coeffs.γ s (X.X s ω') e)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω')) :=
    fun k => LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path (hvC k) hγmeas S.X_prog
  have hCq : ∀ (k : ℕ) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω + coeffs.γ s (X.X s ω) e)
            - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun k T' hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top (hvC k) (hv1 k)
      (fun i => S.γ_meas i) (fun i => S.γ_sq i) hT'
  have hμint : ∀ᵐ ω ∂P, ∀ i : Fin n,
      IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) T) :=
    LevyStochCalc.Ito.JumpFormula.ae_integrableOn_drift_path hμm hμq T
  have hcd : ∀ k : ℕ, ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
        ∂ν ∂volume < ⊤ :=
    fun k => _root_.Prove2MeSourceProof.h_55ca53eaccae9591a8954d60 (hvC k) (hv2 k) hγmeas hXm
      (fun i => S.γ_meas i) (fun i => S.γ_sq i) hT
  -- Step 3: the identity for each mollification.
  have hstep := fun k : ℕ =>
    _root_.Prove2MeSourceProof.h_68143de6ea16052afb9e9c57 W N coeffs x₀ X S hℱ0 hnull0 hXadapt hXleft
      hμm hμp hμq hγmeas (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) (hvC k) (hv0 k) (hv1 k) (hv2 k) T hT hμint
      (hBm k) (hBp k) (hBq k) (hCm k) (hCp k) (hCq k) (hcd k)
  -- Step 4: the Brownian integrals, along a first subsequence.
  have hgBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => max K₁ 0 * ∑ i, |coeffs.σ s (X.X s ω) i j|) := by
    intro j
    change Measurable fun p : Ω × ℝ => max K₁ 0 * ∑ i, |coeffs.σ p.2 (X.X p.2 p.1) i j|
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.σ_meas i j).abs)
  have hgBq : ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖max K₁ 0 * ∑ i, |coeffs.σ s (X.X s ω) i j|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro j
    refine LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X.X s ω) i j)
      (c := max K₁ 0) (fun i => S.σ_meas i j) (fun ω s => ?_) T (fun i => S.σ_sq i j T hT)
    rw [abs_of_nonneg (mul_nonneg hK₁0 (Finset.sum_nonneg fun i _ => abs_nonneg _))]
  have hE : ∀ j : Fin d, Tendsto (fun k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.σ s (X.X s ω) j
        - LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      atTop (𝓝 0) := by
    intro j
    refine _root_.Prove2MeSourceProof.h_8cda0751354c6a4a5b9ce7f5 (fun k => hBm k j) (h_sigmaGrad_meas j)
      (hgBm j) ?_ ?_ (hgBq j)
    · exact Eventually.of_forall fun ω => Eventually.of_forall fun s =>
        LevyStochCalc.Ito.JumpFormula.tendsto_diffusionIntegrand_mollifyJoint hφ hu coeffs.σ s (X.X s ω) j
    · refine fun k => Eventually.of_forall fun ω => Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs]
      exact LevyStochCalc.Ito.JumpFormula.abs_mixedDiffusionIntegrand_le (hv1' k) s _ _ j
  obtain ⟨k₁, hk₁, hk₁ae⟩ := _root_.Prove2MeSourceProof.h_e6dcd6270ba2ccc8443bc922 (ι := Fin d)
    (fun j => W.W j) S.ℱ S.isBrownian
    (fun k j ω s => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.σ s (X.X s ω) j)
    (fun j ω s => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω) j) hBm hBp hBq
    h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq hT hE
  -- Step 4': the compensated jump integrals, along a second subsequence.
  have hgCm : Measurable fun p : Ω × ℝ × E =>
      (n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i| :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.γ_meas i).abs)
  have hgCq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖(n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ s (X.X s ω) e i|‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ := by
    refine _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909
      (a := fun i ω s e => coeffs.γ s (X.X s ω) e i) (c := (n : ℝ) * max K₁ 0)
      (fun i => S.γ_meas i) (fun ω s e => ?_) T (fun i => S.γ_sq i T hT)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hK₁0)
      (Finset.sum_nonneg fun i _ => abs_nonneg _))]
  have hptC : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun i => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω + coeffs.γ s (X.X s ω) e)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω)) atTop
      (𝓝 (u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω))) :=
    Eventually.of_forall fun ω => Eventually.of_forall fun s => Eventually.of_forall fun e =>
      LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le
        (LevyStochCalc.Ito.JumpFormula.tendsto_sub_mollifyJoint hφ hu s (X.X s ω + coeffs.γ s (X.X s ω) e) (X.X s ω)) hk₁
  have hdomC : ∀ i : ℕ, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω + coeffs.γ s (X.X s ω) e)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω)‖
        ≤ (n : ℝ) * max K₁ 0 * ∑ p, |coeffs.γ s (X.X s ω) e p| := by
    refine fun i => Eventually.of_forall fun ω => Eventually.of_forall fun s =>
      Eventually.of_forall fun e => ?_
    rw [Real.norm_eq_abs]
    exact LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le (hvC (k₁ i)) (hv1' (k₁ i)) hK₁0 s _ _ e
  obtain ⟨k₂, _, hk₂, hk₂ae⟩ :=
    _root_.Prove2MeSourceProof.h_225f75f07ee472595cebf470 N S.ℱ S.isPoisson
      (fun i ω s e => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω + coeffs.γ s (X.X s ω) e)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ i)) s (X.X s ω))
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
      (fun ω s e => (n : ℝ) * max K₁ 0 * ∑ p, |coeffs.γ s (X.X s ω) e p|)
      (fun i => hCm (k₁ i)) (fun i => hCp (k₁ i)) (fun i => hCq (k₁ i))
      h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq hgCm hT hptC hdomC hgCq
  have hcomp : ∀ i : ℕ, i ≤ k₁ (k₂ i) := LevyStochCalc.Ito.JumpFormula.le_comp_of_le hk₁ hk₂
  -- Step 5: the two Lebesgue integrals, and the limit identity along the composite subsequence.
  have hdrift := _root_.Prove2MeSourceProof.h_d628dfa7650ec50fbda91fa8 S hu hK₀ hK₁ hK₂ hμm hμq T hT φ hφ
  have hcdrift := _root_.Prove2MeSourceProof.h_480386ee1a4adafe3cb7c0b7 S hu hK₂ T hT φ hφ
  filter_upwards [MeasureTheory.ae_all_iff.mpr hstep, hdrift, hcdrift, hk₁ae, hk₂ae]
    with ω h1 h2 h3 h4 h5
  have hend : Tendsto (fun i => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ (k₂ i))) T (X.X T ω)
      - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ (k₂ i))) 0 (X.X 0 ω)) atTop
      (𝓝 (u T (X.X T ω) - u 0 (X.X 0 ω))) :=
    LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le ((LevyStochCalc.Ito.JumpFormula.tendsto_mollifyJoint hφ hu.continuous T (X.X T ω)).sub
      (LevyStochCalc.Ito.JumpFormula.tendsto_mollifyJoint hφ hu.continuous 0 (X.X 0 ω))) hcomp
  have hbro : Tendsto (fun i =>
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W S.ℱ S.isBrownian
        (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ (k₁ (k₂ i)))) coeffs.σ s (X.X s ω))
        (hBm (k₁ (k₂ i))) (hBp (k₁ (k₂ i))) (hBq (k₁ (k₂ i))) T ω) atTop
      (𝓝 (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W S.ℱ S.isBrownian (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω))
        h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)) := by
    simp only [multidimStochasticIntegral_eq_sum]
    exact tendsto_finsetSum _ fun j _ => LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le (h4 j) hk₂
  have hLHS := (hend.sub (LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le h2 hcomp)).sub hbro
  have hRHS := h5.add (LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le h3 hcomp)
  exact tendsto_nhds_unique (hLHS.congr fun i => h1 (k₁ (k₂ i))) hRHS
end Main

end LevyStochCalc.Ito.JumpFormula


