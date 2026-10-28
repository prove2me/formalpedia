-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardStepMap
-- name    : KLSModular_LevyStochCalc_Ito_PicardStepMap
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:23:50.101004+00:00
-- url     : https://prove2.me/theorems/21926b6e-8177-414a-981c-1a2486aea5bd
-- title:
--   The jump-diffusion Picard step map
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `picardStep_diffusion` is the row-wise sum of multidimensional Brownian Itô integrals of $\sigma(s,X_s)$, and `picardStep_jump` is the row-wise compensated-Poisson integral of $\gamma(s,X_s,e)$; their explicit measurability, progressive-measurability, and finite squared-energy hypotheses are parameters. `picardStep` is the vector-valued sum of the initial state, `picardStep_drift`, the diffusion component, and the jump component. The bundle also includes an integrated squared bound for the drift difference in $[0,\infty]$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardBieleckiNorm
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def picardStep_diffusion
--       {P : MeasureTheory.Measure Ω}
--       [MeasureTheory.IsProbabilityMeasure P]
--       {n d : ℕ}
--       (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
--       (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
--       (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
--       (X : ℝ → Ω → (Fin n → ℝ))
--       -- Per-row joint measurability of σ along X.
--       (h_meas : ∀ i : Fin n, ∀ j : Fin d,
--         Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
--       -- Progressive measurability wrt W component j's natural filtration.
--       (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
--           Probability.ProgressivelyMeasurable ℱ
--             (fun ω s => coeffs.σ s (X s ω) i j))
--       -- Per-row, per-component L² boundedness on every finite horizon.
--       (h_sq_int_global : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (t : ℝ) (ω : Ω) : Fin n → ℝ
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardStepMap.lean) · `LevyStochCalc.Ito.PicardStepMap` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardStepMap.lean#L81-L509 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardStepMap`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardStepMap`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardBieleckiNorm

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardStepMap.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
omit [MeasurableSpace E] in
/-- **Drift step L² Lipschitz: integrated form (lintegral over ω).**

Take the lintegral of the sum-of-squares pointwise bound from
`picardStep_drift_diff_sum_sq_bound`. Using monotonicity of `∫⁻`
(the lemma `MeasureTheory.lintegral_mono_ae` applied to the pointwise
bound that holds for a.e. ω), we get:

  `∫⁻ ω, (∑ i, ((drift X - drift Y) i)²)
    ≤ n · L_μ² · t · ∫⁻ ω, ∫ s in [0, t], ‖X-Y‖² ds`.

The conversion from the real-valued pointwise bound to the ℝ≥0∞-valued
lintegral form uses `ENNReal.ofReal_le_ofReal` and the nonnegativity
of all the integrands.

This is the operator-level (probability-measure-integrated) bound that
sits one step away from the Bielecki β-norm contraction. -/
lemma picardStep_drift_diff_lintegral_sq_bound
    {n d : ℕ} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    (_h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    -- Almost-everywhere integrability hypotheses (the pointwise bound only
    -- holds for ω with all integrands well-defined):
    (h_bound_ae : ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L_μ ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- Nonnegativity of the per-ω inner integral (for ENNReal conversion):
    (h_inner_nn : ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal
          (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  -- Monotonicity of lintegral applied to the a.e. bound.
  have h_pointwise_ennreal : ∀ᵐ ω ∂P,
      ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
    filter_upwards [h_bound_ae, h_inner_nn] with ω h_bd h_inner_nn
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) * L_μ ^ 2 * t)]
    exact ENNReal.ofReal_le_ofReal h_bd
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae h_pointwise_ennreal
    _ = ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-- **Picard map diffusion component (σ row i along X).**

For row `i : Fin n`, the diffusion component is
`∫_0^t (σ(s, X_s) i) · dW_s`, i.e., the multidim Brownian Itô integral
of `Z_i(s, ω) := fun j => σ(s, X(s,ω)) i j` against `W`.

Built using `MultidimBrownianMotion.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq_int_global` propagate from joint-measurability
+ progressive-measurability + L²-boundedness of σ along X, which in turn
follow from the corresponding hypotheses on X and σ. -/
noncomputable def picardStep_diffusion
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint measurability of σ along X.
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    -- Progressive measurability wrt W component j's natural filtration.
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    -- Per-row, per-component L² boundedness on every finite horizon.
    (h_sq_int_global : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
    W ℱ hℱW
    (fun s ω' => fun j => coeffs.σ s (X s ω') i j)
    (h_meas i) (h_progMeas i) (h_sq_int_global i) t ω
/-- **Picard map jump component (γ row i along X compensated-Poisson integral).**

For row `i : Fin n`, the jump component is
`∫_0^t ∫_E γ(s, X_s, e) i Ñ(ds, de)`, i.e., the compensated-Poisson
integral of `(s, e, ω) ↦ γ(s, X(s,ω), e) i` against `Ñ`.

Built using `Compensated.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq` propagate from joint Ω×ℝ×E-measurability
+ progressive-measurability + L²-boundedness of γ along X. -/
noncomputable def picardStep_jump
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint Ω×ℝ×E measurability.
    (h_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    -- Per-row progressive measurability wrt N's natural filtration.
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    -- Per-row L² boundedness on every finite horizon.
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
    (fun ω' s e => coeffs.γ s (X s ω') e i)
    (h_meas i) (h_progMeas i) (h_sq i) t ω
/-- **The full Picard map.** Combines the drift, diffusion (Brownian),
and jump (compensated-Poisson) components:

  `Φ X t ω = x₀ + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
          + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`

The `x₀ +` is already in `picardStep_drift`; here we add the diffusion
and jump components.

This is the literature Picard map for the jump-diffusion SDE (Applebaum
6.2.9 / Ikeda-Watanabe IV). The hypotheses required to make all three
components well-typed are bundled as explicit parameters. -/
noncomputable def picardStep
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral.
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses for the compensated-Poisson integral.
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  picardStep_drift coeffs X x₀ t ω
    + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω
    + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω
end Picard
end Ito
end LevyStochCalc


