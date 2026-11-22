-- Prove2me | Definitions.Def_NonvacuityItoLevyPath_F000
-- name    : NonvacuityItoLevyPath_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:04:11.544903+00:00
-- url     : https://prove2.me/theorems/87a86bb0-7fdc-4013-b242-69dfcbebde1b
-- title:
--   Source declarations: NonvacuityItoLevyPath
-- statement:
--   Source-preserving extracted declarations from NonvacuityItoLevyPath. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F000
import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
import Definitions.Def_LevyStochCalc_Probability_Augmentation_F000
import Definitions.Def_NonvacuityItoLevy_F000
import Definitions.Def_SourceProof_3d27237b32316a1fa19a9df4
import Definitions.Def_SourceProof_a1d63148328e300a17a03a3d
import Definitions.Def_SourceProof_cbb0fd7558e885b374c4446f

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

/-- The drift of the coefficients of the scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`
vanishes. -/
theorem coeffs_mu_apply (s : ℝ) (x : Fin 1 → ℝ) (i : Fin 1) : coeffs.μ s x i = 0 := rfl
/-! ### A cross witness at the augmented right-continuation -/

/-- The right-continuation of a filtration is monotone in the filtration. -/
theorem rightCont_mono_of_le {Ω : Type u} {m : MeasurableSpace Ω}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ m} (h : ∀ t : ℝ, ℱ t ≤ 𝒢 t) (t : ℝ) :
    ℱ.rightCont t ≤ 𝒢.rightCont t := by
  rw [ℱ.rightCont_eq t, 𝒢.rightCont_eq t]
  exact iInf₂_mono fun j _ => h j
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The cross witness of a Lévy driver at the filtration obtained by right-continuing and then
augmenting by the null sets. -/
noncomputable def crossWitnessAugRightCont {E : Type v} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] {d : ℕ} {D : LevyDriver P d ν}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (𝒲 : D.CrossWitness ℱ) :
    D.CrossWitness (Brownian.augFiltration ℱ.rightCont P) where
  poissonLarger := Brownian.augFiltration 𝒲.poissonLarger.rightCont P
  poisson_le := fun _ => Probability.aug_mono (rightCont_mono_of_le 𝒲.poisson_le _)
  isPoisson := Poisson.isPoissonFiltration_augFiltration (_root_.Prove2MeSourceProof.h_cbb0fd7558e885b374c4446f 𝒲.isPoisson)
  measurable_increment := fun i s p q =>
    (𝒲.measurable_increment i s p q).mono
      ((𝒲.poissonLarger.le_rightCont s).trans
        (Brownian.le_augFiltration 𝒲.poissonLarger.rightCont P s)) le_rfl
  brownianLarger := Brownian.augFiltration 𝒲.brownianLarger.rightCont P
  brownian_le := fun _ => Probability.aug_mono (rightCont_mono_of_le 𝒲.brownian_le _)
  isBrownian := fun i => Brownian.isBrownianFiltration_augFiltration (_root_.Prove2MeSourceProof.h_3d27237b32316a1fa19a9df4 (𝒲.isBrownian i))
  stronglyMeasurable_compensated := fun s _ hB =>
    (𝒲.stronglyMeasurable_compensated s hB).mono
      ((𝒲.brownianLarger.le_rightCont s).trans
        (Brownian.le_augFiltration 𝒲.brownianLarger.rightCont P s))
/-! ### The second moment of a solution at time `1` -/

section Solution

variable {D : LevyDriver P 1 jumpIntensity}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → (Fin 1 → ℝ)}

/-- The single coordinate of a path solving the jump-diffusion equation of `coeffs` from `0`,
with its drift, diffusion and jump coefficients along the path, is an Itô–Lévy process. -/
theorem isItoLevyProcess_of_solvesOn (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    IsItoLevyProcess D.W D.N ℱ hℱW hℱN (fun t ω => X t ω 0) (fun _ => (0 : ℝ))
      (fun s ω => coeffs.μ s (X s ω) 0) (fun s ω => coeffs.σ s (X s ω) 0)
      (fun ω s e => coeffs.γ s (X s ω) e 0) := by
  refine ⟨hXm.eval, fun j => (hXsol 0).h_σ_meas 0 j, fun j => (hXsol 0).h_σ_progMeas 0 j,
    fun j => (hXsol 0).h_σ_sq 0 j, (hXsol 0).h_γ_meas 0, (hXsol 0).h_γ_progMeas 0,
    (hXsol 0).h_γ_sq 0, ?_⟩
  intro t ht
  filter_upwards [eqn_sum_form D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) (hXsol t)
    ⟨ht, le_rfl⟩] with ω hω
  exact hω 0
end Solution

/-! ### The filtration of the construction -/

variable (D : LevyDriver P 1 jumpIntensity)

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


