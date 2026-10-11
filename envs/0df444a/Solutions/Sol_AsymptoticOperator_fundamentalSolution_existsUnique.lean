-- Prove2me | solution 1 for AsymptoticOperator.fundamentalSolution_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:27:53.32513+00:00
-- url     : https://prove2.me/submissions/31f988a9-aa64-4d4a-9294-aa6e6dac2a7d

import Definitions.Def_AsymptoticOperator_Setting
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique

open ConleyZehnder AsymptoticOperator

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃! Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let A : ℝ → Mat n := fun t => J₀ n * S (t : UnitAddCircle)
  have hA : Continuous A :=
    continuous_const.mul (S.continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
  let B : ℝ → Mat n →L[ℝ] Mat n :=
    fun t => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (A t))
  have hB : Continuous B := by
    refine continuous_clm_apply.2 fun y => ?_
    exact hA.mul continuous_const
  obtain ⟨Ψ, ⟨hΨ0, hΨ⟩, huniq⟩ := linearODE_existsUnique B hB 1
  exact ⟨Ψ, ⟨hΨ0, hΨ⟩, fun Φ hΦ => huniq Φ ⟨hΦ.1, hΦ.2⟩⟩
