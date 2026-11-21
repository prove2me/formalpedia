-- Prove2me | Definitions.Def_SourceProof_062bf24d9942f2f625b4c411
-- name    : SourceProof_062bf24d9942f2f625b4c411
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:55.626012+00:00
-- url     : https://prove2.me/theorems/7830ddbe-7b0b-4ace-8df4-b101e12697b1
-- title:
--   LevyStochCalc source module: SourceProof_062bf24d9942f2f625b4c411
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.isItoVersion_trig` comes from the `LevyStochCalc.Brownian.CellCharacter` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The trigonometric functions of a Brownian increment are Itô processes

For a continuous version `X` of `∫ 1_{(a,b]} dW`, Itô's formula for the scaled cosine and sine
says that `cos (l X)` and `sin (l X)` are themselves Itô processes: their integrands are
`∓ l sin (l X) 1_{(a,b]}` and `± l cos (l X) 1_{(a,b]}` and their drifts are
`−(l²/2) cos (l X) 1_{(a,b]}²` and `−(l²/2) sin (l X) 1_{(a,b]}²`, with initial value `1` and `0`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_062bf24d9942f2f625b4c411
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T : ℝ, 0 < T →
      (fun ω : Ω => g (l * X T ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) :
    IsItoVersion W ℱ hℱ (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg
      (fun _ => g 0) (trigDriftCell l (fun x => g (l * x)) X a b)
      (fun t ω => g (l * X t ω)) where
  continuous_path ω := hgc.comp ((continuous_const.mul (hX.continuous_path ω)))
  adapted t := hgc.comp_stronglyMeasurable
    ((continuous_const.mul continuous_id).comp_stronglyMeasurable (hX.adapted t))
  ae_eq t ht := by
    have hglc : Continuous fun x : ℝ => g (l * x) :=
      hgc.comp (continuous_const.mul continuous_id)
    have hbm := LevyStochCalc.Brownian.Ito.measurable_trigDriftCell hX l (g := fun x : ℝ => g (l * x)) hglc
    rcases eq_or_lt_of_le ht with rfl | ht'
    · filter_upwards [hX0, _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ _ hmg hpg hqg
        (le_refl (0 : ℝ))] with ω h0 hI
      have hz : (∫ s in Set.Icc (0 : ℝ) 0,
          LevyStochCalc.Brownian.Ito.trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) = 0 := by
        rw [show Set.Icc (0 : ℝ) 0 = {0} from Set.Icc_self 0,
          setIntegral_measure_zero _ Real.volume_singleton]
      change g (l * X 0 ω) = _
      unfold LevyStochCalc.Brownian.Ito.itoProcess
      rw [hz, hI, h0]
      norm_num
    · filter_upwards [hito t ht', hX0] with ω hω h0
      unfold LevyStochCalc.Brownian.Ito.itoProcess
      have hdrift : (∫ s in Set.Icc (0 : ℝ) t,
            LevyStochCalc.Brownian.Ito.trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume)
          = 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) t,
              (-l ^ 2 * g (l * X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s ^ 2 ∂volume := by
        rw [integral_Icc_eq_integral_Ioc]
        unfold LevyStochCalc.Brownian.Ito.trigDriftCell
        rw [integral_const_mul]
      rw [hdrift]
      have h1 : g (l * X t ω) - g (l * X 0 ω) = _ := hω
      rw [h0] at h1
      simp only [mul_zero] at h1
      linarith [h1]
end Version

end LevyStochCalc.Brownian.Ito


