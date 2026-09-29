-- Prove2me | solution 1 for AkhmedovNeutrino.matter_eigenstates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T10:20:26.276588+00:00
-- url     : https://prove2.me/submissions/02a809ca-8794-49c3-9901-9e5dc1ed57ee

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false
set_option linter.unusedVariables false

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF Ne θ : ℝ) (hE : 0 < E)
    (hcos : matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
      Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)
    (hsin : matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
      Δm2 / (2 * E) * Real.sin (2 * θ0)) :
    (mswHamiltonian Δm2 E θ0 GF Ne).mulVec ![Real.cos θ, -Real.sin θ] =
        ((ccPotential GF Ne - matterEnergyGap Δm2 E θ0 GF Ne) / 2) •
          ![Real.cos θ, -Real.sin θ] ∧
    (mswHamiltonian Δm2 E θ0 GF Ne).mulVec ![Real.sin θ, Real.cos θ] =
        ((ccPotential GF Ne + matterEnergyGap Δm2 E θ0 GF Ne) / 2) •
          ![Real.sin θ, Real.cos θ] := by
  have hC := Real.cos_two_mul θ
  have hS := Real.sin_two_mul θ
  have hp := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i
    · simp only [mswHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      linear_combination (1 / 2 : ℝ) * (Real.cos θ * hcos + Real.sin θ * hsin -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hC -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.sin θ * hS -
        2 * matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hp)
    · simp only [mswHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      linear_combination (1 / 2 : ℝ) * (Real.sin θ * hcos - Real.cos θ * hsin +
        matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hS -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.sin θ * hC)
  · ext i
    fin_cases i
    · simp only [mswHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      linear_combination (1 / 2 : ℝ) * (Real.sin θ * hcos - Real.cos θ * hsin +
        matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hS -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.sin θ * hC)
    · simp only [mswHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      linear_combination (-1 / 2 : ℝ) * (Real.cos θ * hcos + Real.sin θ * hsin -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hC -
        matterEnergyGap Δm2 E θ0 GF Ne * Real.sin θ * hS -
        2 * matterEnergyGap Δm2 E θ0 GF Ne * Real.cos θ * hp)
