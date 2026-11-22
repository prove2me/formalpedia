-- Prove2me | Definitions.Def_NonvacuityJumpDiffusionCited_F000
-- name    : NonvacuityJumpDiffusionCited_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:22:27.800174+00:00
-- url     : https://prove2.me/theorems/ee79e45e-9128-4421-ae1d-cd26587277de
-- title:
--   Source declarations: NonvacuityJumpDiffusionCited
-- statement:
--   Source-preserving extracted declarations from NonvacuityJumpDiffusionCited. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
import Definitions.Def_NonvacuityItoLevyPath_F001
import Definitions.Def_SourceProof_d86b93a1720501bd3dee4555

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence and uniqueness for the scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`

The coefficients `coeffs` (`μ = 0`, `σ = 1`, `γ(s, x, e) = e`), the jump intensity `δ₁` and the
initial condition `0` satisfy the Lipschitz and regularity hypotheses of the jump-diffusion
existence and uniqueness theorem, and the augmented right-continuation of the joint filtration of
a Lévy driver satisfies the usual conditions and carries both driver properties. The jump
diffusion the theorem produces has second moment `2` in its single coordinate at time `1`, hence
is not almost surely `0` there, and so is every jump diffusion solving the same equation
relative to the same filtration.

## Main statements

* `integral_sq_jumpDiffusion_one` — the second moment `2` at time `1`, whence
  `jumpDiffusion_value_one_not_ae_zero` and `jumpDiffusion_state_one_not_ae_zero`.
* `picard_jumpDiffusion_model_exists_unique` — the conclusion of
  `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` on this data, together
  with the second moment of the produced solution and of every competitor.
* `jumpDiffusion_model_exists_unique` — the same data through the literature-facing form
  `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique`.
* `exists_jumpDiffusion_cited` — the same statements on a probability space delivered by the
  existence theorem for Lévy drivers.

## References

* Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., Cambridge University Press,
  2009, Theorem 6.2.9.
* Ikeda, N. & Watanabe, S. *Stochastic Differential Equations and Diffusion Processes*,
  North-Holland, 1989, Chapter IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Ito.Picard (SolvesOn)
open LevyStochCalc.Ito.Setting (JumpDiffusion)

universe u

section Model

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (D : LevyDriver P 1 jumpIntensity)

/-! ### The usual conditions at the filtration of the construction -/

/-- The augmented right-continuation of the driver's joint filtration is constant on the
nonpositive times. -/
theorem augRightCont_le_of_nonpos (t : ℝ) (ht : t ≤ 0) :
    Brownian.augFiltration D.filtration.rightCont P 0
      ≤ Brownian.augFiltration D.filtration.rightCont P t :=
  le_of_eq (Brownian.augFiltration_of_nonpos D.filtration.rightCont P ht).symm
/-- The augmented right-continuation of the driver's joint filtration contains every null set at
time `0`. -/
theorem measurableSet_augRightCont_of_null (s : Set Ω) (hs : MeasurableSet s) (h0 : P s = 0) :
    MeasurableSet[Brownian.augFiltration D.filtration.rightCont P 0] s :=
  Brownian.measurableSet_augFiltration_of_null D.filtration.rightCont P hs h0
/-- The augmented right-continuation of the driver's joint filtration is right-continuous. -/
instance isRightContinuous_augRightCont :
    (Brownian.augFiltration D.filtration.rightCont P).IsRightContinuous :=
  Brownian.isRightContinuous_augFiltration D.filtration P
/-! ### The second moment of a jump diffusion at time `1` -/

variable (jd : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ))

/-- The second moment at time `1` of the single coordinate of a jump diffusion for `coeffs`
started at `0`, solving the integral equation relative to the augmented right-continuation of the
driver's joint filtration, is `2`. -/
theorem integral_sq_jumpDiffusion_one
    (hsol : ∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
      (0 : Fin 1 → ℝ) jd.X T) :
    ∫ ω, jd.X 1 ω 0 * jd.X 1 ω 0 ∂P = 2 :=
  _root_.Prove2MeSourceProof.h_296afdeae0e2497c44a27c1c (crossWitnessAugRightCont D.crossWitness) jd.measurable_path hsol
/-- The single coordinate at time `1` of such a jump diffusion is not almost surely `0`. -/
theorem jumpDiffusion_value_one_not_ae_zero
    (hsol : ∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
      (0 : Fin 1 → ℝ) jd.X T) :
    ¬ ((fun ω => jd.X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) :=
  solvesOn_augRightCont_value_one_not_ae_zero D jd.measurable_path hsol
/-- The state at time `1` of such a jump diffusion is not almost surely `0`. -/
theorem jumpDiffusion_state_one_not_ae_zero
    (hsol : ∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
      (0 : Fin 1 → ℝ) jd.X T) :
    ¬ ((fun ω => jd.X 1 ω) =ᵐ[P] fun _ => (0 : Fin 1 → ℝ)) := by
  intro h
  refine jumpDiffusion_value_one_not_ae_zero D jd hsol ?_
  filter_upwards [h] with ω hω
  simp [hω]
/-! ### The cited theorems on this data -/

/-- **The scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)` from `0` exists, is unique and is
not almost surely `0` at time `1`.** For the augmented right-continuation `ℱ` of the driver's
joint filtration there is a jump diffusion for `coeffs` started at `0` solving the integral
equation relative to `ℱ` at every horizon, whose single coordinate at time `1` has second moment
`2` and whose state at time `1` is not almost surely `0`; every jump diffusion solving the same
equation relative to `ℱ` agrees with it almost surely at every `t ≥ 0` and likewise has a single
coordinate at time `1` that is not almost surely `0`. -/
theorem picard_jumpDiffusion_model_exists_unique :
    ∃ jd : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ),
      (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
          (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
          (0 : Fin 1 → ℝ) jd.X T)
        ∧ (∫ ω, jd.X 1 ω 0 * jd.X 1 ω 0 ∂P = 2)
        ∧ ¬ ((fun ω => jd.X 1 ω) =ᵐ[P] fun _ => (0 : Fin 1 → ℝ))
        ∧ ∀ jd' : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ),
            (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
                (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D)
                coeffs (0 : Fin 1 → ℝ) jd'.X T) →
              (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω)
                ∧ ¬ ((fun ω => jd'.X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨jd, hsol, huniq⟩ :=
    LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique D.W D.N
      (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D)
      (augRightCont_le_of_nonpos D) (measurableSet_augRightCont_of_null D) coeffs
      (0 : Fin 1 → ℝ) coeffs_isLipschitz _root_.Prove2MeSourceProof.h_fbf2bdb2e46963ef0b18b08d
  exact ⟨jd, hsol, integral_sq_jumpDiffusion_one D jd hsol,
    jumpDiffusion_state_one_not_ae_zero D jd hsol,
    fun jd' hsol' =>
      ⟨huniq jd' hsol', jumpDiffusion_value_one_not_ae_zero D jd' hsol'⟩⟩
/-- **The literature form of the previous statement.** For the augmented right-continuation `ℱ`
of the driver's joint filtration the jump-diffusion SDE with coefficients `coeffs` and initial
condition `0` has a solution relative to `ℱ`, unique up to almost-sure equality at every `t ≥ 0`,
whose single coordinate at time `1` has second moment `2` and is not almost surely `0`. -/
theorem jumpDiffusion_model_exists_unique :
    ∃ jd : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ),
      (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
          (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
          (0 : Fin 1 → ℝ) jd.X T)
        ∧ (∀ jd' : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ),
            (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
                (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D)
                coeffs (0 : Fin 1 → ℝ) jd'.X T) →
              ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω)
        ∧ (∫ ω, jd.X 1 ω 0 * jd.X 1 ω 0 ∂P = 2)
        ∧ ¬ ((fun ω => jd.X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨jd, hsol, huniq⟩ :=
    _root_.Prove2MeSourceProof.h_d86b93a1720501bd3dee4555 D.W D.N
      (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D)
      (augRightCont_le_of_nonpos D) (measurableSet_augRightCont_of_null D) coeffs
      (0 : Fin 1 → ℝ) coeffs_isLipschitz _root_.Prove2MeSourceProof.h_fbf2bdb2e46963ef0b18b08d
  exact ⟨jd, hsol, huniq, integral_sq_jumpDiffusion_one D jd hsol,
    jumpDiffusion_value_one_not_ae_zero D jd hsol⟩
end Model

/-! ### The witness -/

/-- **A jump diffusion of the scalar Itô–Lévy model on a probability space carrying a Lévy
driver.** On some probability space there are a Lévy driver with intensity `δ₁` and a jump
diffusion `jd` for `coeffs` started at `0` solving the integral equation at every horizon,
relative to the augmented right-continuation of the driver's joint filtration, whose single
coordinate at time `1` has second moment `2` and whose state at time `1` is not almost surely
`0`; every jump diffusion solving the same equation agrees with `jd` almost surely at every
`t ≥ 0` and has a single coordinate at time `1` that is not almost surely `0`. -/
theorem exists_jumpDiffusion_cited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 jumpIntensity)
      (jd : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ)),
      (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
          (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
          (0 : Fin 1 → ℝ) jd.X T)
        ∧ (∫ ω, jd.X 1 ω 0 * jd.X 1 ω 0 ∂P = 2)
        ∧ ¬ ((fun ω => jd.X 1 ω) =ᵐ[P] fun _ => (0 : Fin 1 → ℝ))
        ∧ ∀ jd' : JumpDiffusion D.W D.N coeffs (0 : Fin 1 → ℝ),
            (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
                (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D)
                coeffs (0 : Fin 1 → ℝ) jd'.X T) →
              (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω)
                ∧ ¬ ((fun ω => jd'.X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyDriver.exists 1 ℝ jumpIntensity
  obtain ⟨jd, hsol, hmom, hstate, huniq⟩ := picard_jumpDiffusion_model_exists_unique D
  exact ⟨Ω, inferInstance, P, inferInstance, D, jd, hsol, hmom, hstate, huniq⟩
end LevyStochCalc.Examples.Nonvacuity


