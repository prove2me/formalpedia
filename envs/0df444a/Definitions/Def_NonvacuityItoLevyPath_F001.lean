-- Prove2me | Definitions.Def_NonvacuityItoLevyPath_F001
-- name    : NonvacuityItoLevyPath_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:17:19.20472+00:00
-- url     : https://prove2.me/theorems/8f90df89-c46e-4a73-b071-d61a77789afa
-- title:
--   Source declarations: NonvacuityItoLevyPath
-- statement:
--   Source-preserving extracted declarations from NonvacuityItoLevyPath. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Definitions.Def_NonvacuityItoLevyPath_F000
import Definitions.Def_NonvacuityItoLevy_F001
import Definitions.Def_SourceProof_296afdeae0e2497c44a27c1c
import Definitions.Def_SourceProof_98d5b80f0fbd482e08c8d6f3
import Definitions.Def_SourceProof_fbf2bdb2e46963ef0b18b08d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The value at time `1` of the jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`

For the coefficients `coeffs` (`μ = 0`, `σ = 1`, `γ(s, x, e) = e`) and the jump intensity
`δ₁`, a path solving the jump-diffusion integral equation from `0` relative to a filtration
carrying both driver properties has second moment `2` in its single coordinate at time `1`:
the drift vanishes, the Brownian leg contributes `∫_0^1 1 ds = 1`, the compensated leg
contributes `∫_0^1 ∫_ℝ e² δ₁(de) ds = 1`, and the two legs are orthogonal. In particular that
coordinate is not almost surely `0` at time `1`.

The second moment is the expectation form of the quadratic Itô formula,
`LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess`, whose orthogonality
input is a cross witness for the filtration; `crossWitnessAugRightCont` carries the driver's
own witness to the augmented right-continuation of the joint filtration, the filtration at
which `LevyStochCalc.Ito.Picard.exists_globalSolution` produces a solution.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Ito.Picard (SolvesOn eqn_sum_form)
open LevyStochCalc.Ito.Setting (IsItoLevyProcess)

universe u v

/-! ### A cross witness at the augmented right-continuation -/

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The second moment of a solution at time `1` -/

section Solution

variable {D : LevyDriver P 1 jumpIntensity}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → (Fin 1 → ℝ)}

/-- The single coordinate at time `1` of a path solving the jump-diffusion equation of `coeffs`
from `0` is not almost surely `0`. -/
theorem solvesOn_value_one_not_ae_zero (𝒲 : D.CrossWitness ℱ)
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  intro h
  have hzero : (fun ω => X 1 ω 0 * X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 : ∫ ω, X 1 ω 0 * X 1 ω 0 ∂P = 0 := by
    rw [integral_congr_ae hzero, integral_zero]
  rw [_root_.Prove2MeSourceProof.h_296afdeae0e2497c44a27c1c 𝒲 hXm hXsol] at h0
  norm_num at h0
end Solution

/-! ### The filtration of the construction -/

variable (D : LevyDriver P 1 jumpIntensity)

/-- Every coordinate of the driver's Brownian motion is a Brownian motion for the augmented
right-continuation of the joint filtration. -/
theorem isBrownianFiltration_augRightCont (j : Fin 1) :
    Brownian.IsBrownianFiltration (D.W.W j)
      (Brownian.augFiltration D.filtration.rightCont P) :=
  Brownian.isBrownianFiltration_augFiltration (_root_.Prove2MeSourceProof.h_3d27237b32316a1fa19a9df4 (D.isBrownianFiltration j))
/-- The driver's Poisson random measure is a Poisson random measure for the augmented
right-continuation of the joint filtration. -/
theorem isPoissonFiltration_augRightCont :
    Poisson.IsPoissonFiltration D.N (Brownian.augFiltration D.filtration.rightCont P) :=
  Poisson.isPoissonFiltration_augFiltration (_root_.Prove2MeSourceProof.h_cbb0fd7558e885b374c4446f (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D))
/-- The single coordinate at time `1` of a path solving the jump-diffusion equation of `coeffs`
from `0` relative to the augmented right-continuation of the driver's joint filtration is not
almost surely `0`. -/
theorem solvesOn_augRightCont_value_one_not_ae_zero {X : ℝ → Ω → (Fin 1 → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
      (0 : Fin 1 → ℝ) X T) :
    ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) :=
  solvesOn_value_one_not_ae_zero (crossWitnessAugRightCont D.crossWitness) hXm hXsol
/-! ### The witness -/

/-- **The realised path of the Itô–Lévy example is not almost surely `0` at time `1`.** On some
probability space there are a Lévy driver with intensity `δ₁` and a path `X` solving, at every
horizon and relative to the augmented right-continuation of the driver's joint filtration, the
jump-diffusion equation of `coeffs` from `0`, whose single coordinate at time `1` is not
almost surely `0`. -/
theorem exists_solvesOn_value_one_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 jumpIntensity) (X : ℝ → Ω → (Fin 1 → ℝ)),
      Measurable (Function.uncurry X)
        ∧ (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
            (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
            (0 : Fin 1 → ℝ) X T)
        ∧ ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyDriver.exists 1 ℝ jumpIntensity
  haveI hFrc : (Brownian.augFiltration D.filtration.rightCont P).IsRightContinuous :=
    Brownian.isRightContinuous_augFiltration D.filtration P
  have hℱ0 : ∀ t : ℝ, t ≤ 0 → Brownian.augFiltration D.filtration.rightCont P 0
      ≤ Brownian.augFiltration D.filtration.rightCont P t := fun t ht =>
    le_of_eq (Brownian.augFiltration_of_nonpos D.filtration.rightCont P ht).symm
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      MeasurableSet[Brownian.augFiltration D.filtration.rightCont P 0] s := fun s hs h0 =>
    Brownian.measurableSet_augFiltration_of_null D.filtration.rightCont P hs h0
  obtain ⟨Xp, hXm, _hXa, _hX0, _hXcad, _hXS, hXsol⟩ :=
    _root_.Prove2MeSourceProof.h_a1d63148328e300a17a03a3d D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs hℱ0
      hnull _root_.Prove2MeSourceProof.h_fbf2bdb2e46963ef0b18b08d coeffs_isLipschitz (0 : Fin 1 → ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, Xp, hXm, hXsol,
    solvesOn_augRightCont_value_one_not_ae_zero D hXm hXsol⟩
end LevyStochCalc.Examples.Nonvacuity


