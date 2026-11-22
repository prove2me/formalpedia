-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
-- name    : LevyStochCalc_Ito_PicardWellPosed_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:59:26.782729+00:00
-- url     : https://prove2.me/theorems/89e8906e-975d-49af-8e24-1388a6bcb009
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardWellPosed
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardWellPosed. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F001
import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F002
import Definitions.Def_SourceProof_a1d63148328e300a17a03a3d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Well-posedness of the jump-diffusion SDE

The glued solution of `exists_globalSolution` populates every field of `JumpDiffusion`, and the
window uniqueness of `ae_eq_of_solvesOn` identifies it with any other solution of the equation
relative to the same filtration.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

section WellPosed

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

/-- The window equation in the summed form of `JumpDiffusion.is_solution`. -/
theorem eqn_sum_form {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W ℱ hℱW (fun s ω => coeffs.σ s (X s ω) i)
            (fun j => h.h_σ_meas i j) (fun j => h.h_σ_progMeas i j) (fun j => h.h_σ_sq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω' s e => coeffs.γ s (X s ω') e i)
            (h.h_γ_meas i) (h.h_γ_progMeas i) (h.h_γ_sq i) t ω := by
  filter_upwards [h.eqn t ht] with ω hω
  intro i
  rw [hω i, picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
    h.h_γ_meas h.h_γ_progMeas h.h_γ_sq t ω i]
  rfl
/-- A path map solving the equation on every window, càdlàg and `S²`-bounded, is a
`JumpDiffusion`. -/
noncomputable def jumpDiffusionOfSolvesOn {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀)
    (hXcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hXsol : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀ where
  X := X
  measurable_path := hXm
  initial_value := hX0
  sup_L2 := hXS
  cadlag_paths := hXcad
  is_solution :=
    ⟨ℱ, hℱW, hℱN, (hXsol 0).h_σ_meas, (hXsol 0).h_σ_progMeas, (hXsol 0).h_σ_sq,
      (hXsol 0).h_γ_meas, (hXsol 0).h_γ_progMeas, (hXsol 0).h_γ_sq,
      fun t ht => eqn_sum_form W N ℱ hℱW hℱN coeffs x₀ (hXsol t) ⟨ht, le_rfl⟩⟩
/-- A path map satisfying the integral equation relative to `ℱ` at every `t ≥ 0` solves on every
window. This is the bridge from the summed form of `JumpDiffusion.is_solution`, read at a
particular filtration, to `SolvesOn`. -/
theorem solvesOn_of_eqn {X : ℝ → Ω → (Fin n → ℝ)}
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j)
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i)
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W ℱ hℱW (fun s ω => coeffs.σ s (X s ω) i)
            (fun j => h_σ_meas i j) (fun j => h_σ_progMeas i j) (fun j => h_σ_sq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω' s e => coeffs.γ s (X s ω') e i)
            (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) t ω) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T :=
  ⟨h_σ_meas, h_σ_progMeas, h_σ_sq, h_γ_meas, h_γ_progMeas, h_γ_sq, fun t ht => heq t ht.1⟩
/-- **Well-posedness of the jump-diffusion SDE relative to a filtration satisfying the usual
conditions** (Applebaum 2009 Theorem 6.2.9; Ikeda–Watanabe Chapter IV).

There is a `JumpDiffusion` whose integral equation holds relative to `ℱ`, and any path map
solving the equation relative to the same `ℱ`, with a finite `S²` norm on every window, agrees
with it almost surely at every `t ≥ 0`. -/
theorem exists_jumpDiffusion_unique_of_solvesOn [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L) :
    ∃ jd : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀,
      (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
        ∧ ∀ jd' : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀,
            (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd'.X T) →
              ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  obtain ⟨X, hXm, hXa, hX0, hXcad, hXS, hXsol⟩ :=
    _root_.Prove2MeSourceProof.h_a1d63148328e300a17a03a3d W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀
  refine ⟨jumpDiffusionOfSolvesOn W N ℱ hℱW hℱN coeffs x₀ hXm hX0 hXcad hXS hXsol,
    hXsol, fun jd' hjd' t ht => ?_⟩
  have hpt := _root_.Prove2MeSourceProof.h_48fc762eec2686f4f3c5681d W N ℱ hℱW hℱN coeffs x₀ hReg hLip hXm jd'.measurable_path
    hXS jd'.sup_L2 (by linarith : (0 : ℝ) < t + 1) (hXsol (t + 1)) (hjd' (t + 1))
  filter_upwards [hpt t ⟨ht, by linarith⟩] with ω hω
  exact funext hω
end WellPosed

end LevyStochCalc.Ito.Picard


