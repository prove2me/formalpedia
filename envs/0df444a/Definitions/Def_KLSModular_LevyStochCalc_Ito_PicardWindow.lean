-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
-- name    : KLSModular_LevyStochCalc_Ito_PicardWindow
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:33:07.855928+00:00
-- url     : https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f
-- title:
--   Picard solutions on finite time windows
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `SolvesOn X T` bundles the joint and progressive measurability and finite squared-energy hypotheses for the diffusion and jump integrands, together with the assertion that $X_t$ equals `picardStep` almost everywhere for every $t\in[0,T]$. The bundle also converts a finite supremum-in-time $L^2$ bound into finite integrated energy and supplies progressive measurability and integrability bounds for coefficient compositions. It does not assert existence or uniqueness of a `SolvesOn` witness.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardLocality
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure SolvesOn (X : ℝ → Ω → (Fin n → ℝ)) (T : ℝ) : Prop where
--     /-- Joint measurability of the diffusion integrand along `X`. -/
--     h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
--       Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j)
--     /-- Progressive measurability of the diffusion integrand along `X`. -/
--     h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
--       Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j
--     /-- `L²` boundedness of the diffusion integrand on every finite horizon. -/
--     h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
--       ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
--     /-- Joint measurability of the jump integrand along `X`. -/
--     h_γ_meas : ∀ i : Fin n,
--       Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i
--     /-- Marked progressive measurability of the jump integrand along `X`. -/
--     h_γ_progMeas : ∀ i : Fin n,
--       Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i
--     /-- `L²` boundedness of the jump integrand on every finite horizon. -/
--     h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
--       ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
--         (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
--     /-- The integral equation at every time of the window. -/
--     eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
--       X t ω i = picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
--         h_γ_meas h_γ_progMeas h_γ_sq t ω i
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardLocality`](https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e).
--
--   Theorems in source order:
--
--   - [`bieleckiNorm_lt_top_of_supL2`](https://prove2.me/theorems/2df643b2-8d67-4af3-bd4c-c76523b1d9d8)
--   - [`bieleckiNorm_sub_lt_top_of_lt_top`](https://prove2.me/theorems/02064a85-b521-4d2a-aa86-6273c40d71ff)
--   - [`ae_eq_of_solvesOn`](https://prove2.me/theorems/68acae9c-cef9-4b55-9b63-0571ce263cb6)
--   - [`picardStep_rawStop_congr_ae`](https://prove2.me/theorems/5db0caec-c4f8-4145-9624-8dfa7e854eeb)
--   - [`solvesOn_of_isFixedPoint`](https://prove2.me/theorems/65f806f4-e0d8-4e52-9f10-b2384eb2ab37)
--   - [`exists_solvesOn`](https://prove2.me/theorems/cb1bf20c-3f06-408a-be53-4bceccae12cb)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean) · `LevyStochCalc.Ito.PicardWindow` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L30-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardWindow`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
/-- A process with a finite `S²` norm on every window has finite time-integrated `L²` energy. -/
theorem lintegral_lintegral_sq_lt_top_of_supL2 {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  rcases le_or_gt b 0 with hb | hb
  · have hvol : (volume (Set.Icc (0 : ℝ) b)) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (by linarith : b - 0 ≤ 0)
    have : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume = 0 := by
      intro ω
      exact setLIntegral_measure_zero _ _ hvol
    simp [this]
  · set F : Ω → ℝ≥0∞ :=
      fun ω => ⨆ t : Set.Icc (0 : ℝ) b, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2 with hF
    have hle : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
          ≤ ∫⁻ ω, F ω * ENNReal.ofReal b ∂P := by
      refine lintegral_mono fun ω => ?_
      have hpt : ∫⁻ s in Set.Icc (0 : ℝ) b,
          ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
            ≤ ∫⁻ _ in Set.Icc (0 : ℝ) b, F ω ∂volume := by
        refine setLIntegral_mono_ae ?_ ?_
        · exact measurable_const.aemeasurable
        · refine Filter.Eventually.of_forall fun s hs => ?_
          exact le_iSup (fun t : Set.Icc (0 : ℝ) b =>
            ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨s, hs⟩
      refine hpt.trans ?_
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top (hS b hb) (ENNReal.ofReal_lt_top)
section Solves
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)
/-- `X` satisfies the jump-diffusion integral equation, relative to `ℱ`, at every time of
`[0, T]`. The integrand hypotheses that make the two stochastic integrals well-typed are
bundled existentially, as in `JumpDiffusion.is_solution`. -/
structure SolvesOn (X : ℝ → Ω → (Fin n → ℝ)) (T : ℝ) : Prop where
  /-- Joint measurability of the diffusion integrand along `X`. -/
  h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j)
  /-- Progressive measurability of the diffusion integrand along `X`. -/
  h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j
  /-- `L²` boundedness of the diffusion integrand on every finite horizon. -/
  h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- Joint measurability of the jump integrand along `X`. -/
  h_γ_meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i
  /-- Marked progressive measurability of the jump integrand along `X`. -/
  h_γ_progMeas : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i
  /-- `L²` boundedness of the jump integrand on every finite horizon. -/
  h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The integral equation at every time of the window. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
    X t ω i = picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i
end Solves
section Canonical
variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
omit [IsProbabilityMeasure P] in
/-- Progressive measurability of the diffusion integrand along a progressively measurable
state process. -/
theorem progressivelyMeasurable_sigma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state hXa h
omit [IsProbabilityMeasure P] in
/-- Marked progressive measurability of the jump integrand along a progressively measurable
state process. -/
theorem markedProgressivelyMeasurable_gamma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state
    (g := fun (s : ℝ) (x : Fin n → ℝ) (e : E) => coeffs.γ s x e i) hXa h
/-- The `L²` bound on the diffusion integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_sigma_lt_top_of_supL2
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip hXm
    (lintegral_lintegral_sq_lt_top_of_supL2 hXS) i j hT'
/-- The `L²` bound on the jump integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_gamma_lt_top_of_supL2 [SigmaFinite ν]
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip hXm
    (lintegral_lintegral_sq_lt_top_of_supL2 hXS) i hT'
end Canonical
end Picard
end Ito
end LevyStochCalc


